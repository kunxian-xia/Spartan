#![allow(clippy::too_many_arguments)]
#![allow(clippy::type_complexity)]
use super::commitments::{Commitments, MultiCommitGens};
use super::dense_mlpoly::DensePolynomial;
use super::errors::ProofVerifyError;
use super::group::{CompressedGroup, GroupElement, VartimeMultiscalarMul};
use super::nizk::DotProductProof;
use super::random::RandomTape;
use super::scalar::Scalar;
use super::transcript::{AppendToTranscript, ProofTranscript};
use super::unipoly::{CompressedUniPoly, UniPoly};
use core::iter;
use itertools::izip;
use merlin::Transcript;
use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize, Debug)]
pub struct SumcheckInstanceProof {
  compressed_polys: Vec<CompressedUniPoly>,
}

impl SumcheckInstanceProof {
  pub fn new(compressed_polys: Vec<CompressedUniPoly>) -> SumcheckInstanceProof {
    SumcheckInstanceProof { compressed_polys }
  }

  pub fn verify(
    &self,
    claim: Scalar,
    num_rounds: usize,
    degree_bound: usize,
    transcript: &mut Transcript,
  ) -> Result<(Scalar, Vec<Scalar>), ProofVerifyError> {
    let mut e = claim;
    let mut r: Vec<Scalar> = Vec::new();

    // verify that there is a univariate polynomial for each round
    assert_eq!(self.compressed_polys.len(), num_rounds);
    for i in 0..self.compressed_polys.len() {
      let poly = self.compressed_polys[i].decompress(&e);

      // kunxian: In each round, the prover sends a uni-variate polynomial (in compressed form) to the verifier.

      // verify degree bound
      assert_eq!(poly.degree(), degree_bound);

      // check if G_k(0) + G_k(1) = e
      assert_eq!(poly.eval_at_zero() + poly.eval_at_one(), e);

      // append the prover's message to the transcript
      poly.append_to_transcript(b"poly", transcript);

      //derive the verifier's challenge for the next round
      let r_i = transcript.challenge_scalar(b"challenge_nextround");

      r.push(r_i);

      // evaluate the claimed degree-ell polynomial at r_i
      e = poly.evaluate(&r_i);
    }

    Ok((e, r))
  }
}

#[derive(Serialize, Deserialize, Debug)]
pub struct ZKSumcheckInstanceProof {
  comm_polys: Vec<CompressedGroup>,
  comm_evals: Vec<CompressedGroup>,
  proofs: Vec<DotProductProof>,
}

impl ZKSumcheckInstanceProof {
  pub fn new(
    comm_polys: Vec<CompressedGroup>,
    comm_evals: Vec<CompressedGroup>,
    proofs: Vec<DotProductProof>,
  ) -> Self {
    ZKSumcheckInstanceProof {
      comm_polys,
      comm_evals,
      proofs,
    }
  }

  pub fn verify(
    &self,
    comm_claim: &CompressedGroup,
    num_rounds: usize,
    degree_bound: usize,
    gens_1: &MultiCommitGens,
    gens_n: &MultiCommitGens,
    transcript: &mut Transcript,
  ) -> Result<(CompressedGroup, Vec<Scalar>), ProofVerifyError> {
    // verify degree bound
    assert_eq!(gens_n.n, degree_bound + 1);

    // verify that there is a univariate polynomial for each round
    assert_eq!(self.comm_polys.len(), num_rounds);
    assert_eq!(self.comm_evals.len(), num_rounds);

    // in zk sumcheck protocol, the claimed sum is hidden in a perfect hiding commitment

    let mut r: Vec<Scalar> = Vec::new();
    for i in 0..self.comm_polys.len() {
      let comm_poly = &self.comm_polys[i];

      // kunxian: in each round, the verifier only knows
      //   1. c_es = commit(expected_sum)
      //   2. c_p = commit(p(X)) to the uni-variate polynomial
      //   3. c_r = commit(p(r)) for next round (which is the expected sum for next round).
      //
      // The verifier needs to check that
      // 1. decommit(c_es) = decommit(c_p)(0) + decommit(c_p)(1)
      //      p(0) = a0
      //      p(1) = a0 + ... + a_{degree_bound}
      // 2. decommit(c_r) = decommit(c_p)(r)
      //      p(r) = a0 + a1*r + ... + a_{degree_bound}*r^n
      //
      // For 1
      //  expected_sum = <a, [2,1,1,...,1]>
      // For 2
      //  p(r) = <a, [1, r, r^2, ...]>

      // append the prover's polynomial to the transcript
      comm_poly.append_to_transcript(b"comm_poly", transcript);

      //derive the verifier's challenge for the next round
      let r_i = transcript.challenge_scalar(b"challenge_nextround");

      // verify the proof of sum-check and evals
      let res = {
        let comm_claim_per_round = if i == 0 {
          comm_claim
        } else {
          &self.comm_evals[i - 1]
        };
        let comm_eval = &self.comm_evals[i];

        // add two claims to transcript
        comm_claim_per_round.append_to_transcript(b"comm_claim_per_round", transcript);
        comm_eval.append_to_transcript(b"comm_eval", transcript);

        // produce two weights
        let w = transcript.challenge_vector(b"combine_two_claims_to_one", 2);

        // compute a weighted sum of the RHS
        let comm_target = GroupElement::vartime_multiscalar_mul(
          w.iter(),
          iter::once(&comm_claim_per_round)
            .chain(iter::once(&comm_eval))
            .map(|pt| pt.decompress().unwrap())
            .collect::<Vec<GroupElement>>(),
        )
        .compress();

        let a = {
          // the vector to use to decommit for sum-check test
          let a_sc = {
            let mut a = vec![Scalar::one(); degree_bound + 1];
            a[0] += Scalar::one();
            a
          };

          // the vector to use to decommit for evaluation
          let a_eval = {
            let mut a = vec![Scalar::one(); degree_bound + 1];
            for j in 1..a.len() {
              a[j] = a[j - 1] * r_i;
            }
            a
          };

          // take weighted sum of the two vectors using w
          assert_eq!(a_sc.len(), a_eval.len());
          (0..a_sc.len())
            .map(|i| w[0] * a_sc[i] + w[1] * a_eval[i])
            .collect::<Vec<Scalar>>()
        };

        self.proofs[i]
          .verify(
            gens_1,
            gens_n,
            transcript,
            &a,
            &self.comm_polys[i],
            &comm_target,
          )
          .is_ok()
      };
      if !res {
        return Err(ProofVerifyError::InternalError);
      }

      r.push(r_i);
    }

    Ok((self.comm_evals[self.comm_evals.len() - 1], r))
  }
}

impl SumcheckInstanceProof {
  pub fn prove_cubic<F>(
    claim: &Scalar,
    num_rounds: usize,
    poly_A: &mut DensePolynomial,
    poly_B: &mut DensePolynomial,
    poly_C: &mut DensePolynomial,
    comb_func: F,
    transcript: &mut Transcript,
  ) -> (Self, Vec<Scalar>, Vec<Scalar>)
  where
    F: Fn(&Scalar, &Scalar, &Scalar) -> Scalar,
  {
    let mut e = *claim;
    let mut r: Vec<Scalar> = Vec::new();
    let mut cubic_polys: Vec<CompressedUniPoly> = Vec::new();
    for _j in 0..num_rounds {
      let mut eval_point_0 = Scalar::zero();
      let mut eval_point_2 = Scalar::zero();
      let mut eval_point_3 = Scalar::zero();

      let len = poly_A.len() / 2;
      for i in 0..len {
        // eval 0: bound_func is A(low)
        eval_point_0 += comb_func(&poly_A[i], &poly_B[i], &poly_C[i]);

        // eval 2: bound_func is -A(low) + 2*A(high)
        let poly_A_bound_point = poly_A[len + i] + poly_A[len + i] - poly_A[i];
        let poly_B_bound_point = poly_B[len + i] + poly_B[len + i] - poly_B[i];
        let poly_C_bound_point = poly_C[len + i] + poly_C[len + i] - poly_C[i];
        eval_point_2 += comb_func(
          &poly_A_bound_point,
          &poly_B_bound_point,
          &poly_C_bound_point,
        );

        // eval 3: bound_func is -2A(low) + 3A(high); computed incrementally with bound_func applied to eval(2)
        let poly_A_bound_point = poly_A_bound_point + poly_A[len + i] - poly_A[i];
        let poly_B_bound_point = poly_B_bound_point + poly_B[len + i] - poly_B[i];
        let poly_C_bound_point = poly_C_bound_point + poly_C[len + i] - poly_C[i];

        eval_point_3 += comb_func(
          &poly_A_bound_point,
          &poly_B_bound_point,
          &poly_C_bound_point,
        );
      }

      let evals = vec![eval_point_0, e - eval_point_0, eval_point_2, eval_point_3];
      let poly = UniPoly::from_evals(&evals);

      // append the prover's message to the transcript
      poly.append_to_transcript(b"poly", transcript);

      //derive the verifier's challenge for the next round
      let r_j = transcript.challenge_scalar(b"challenge_nextround");
      r.push(r_j);
      // bound all tables to the verifier's challenege
      poly_A.bound_poly_var_top(&r_j);
      poly_B.bound_poly_var_top(&r_j);
      poly_C.bound_poly_var_top(&r_j);
      e = poly.evaluate(&r_j);
      cubic_polys.push(poly.compress());
    }

    (
      SumcheckInstanceProof::new(cubic_polys),
      r,
      vec![poly_A[0], poly_B[0], poly_C[0]],
    )
  }

  pub fn prove_cubic_batched<F>(
    claim: &Scalar,
    num_rounds: usize,
    poly_vec_par: (
      &mut Vec<&mut DensePolynomial>,
      &mut Vec<&mut DensePolynomial>,
      &mut DensePolynomial,
    ),
    poly_vec_seq: (
      &mut Vec<&mut DensePolynomial>,
      &mut Vec<&mut DensePolynomial>,
      &mut Vec<&mut DensePolynomial>,
    ),
    coeffs: &[Scalar],
    comb_func: F,
    transcript: &mut Transcript,
  ) -> (
    Self,
    Vec<Scalar>,
    (Vec<Scalar>, Vec<Scalar>, Scalar),
    (Vec<Scalar>, Vec<Scalar>, Vec<Scalar>),
  )
  where
    F: Fn(&Scalar, &Scalar, &Scalar) -> Scalar,
  {
    let (poly_A_vec_par, poly_B_vec_par, poly_C_par) = poly_vec_par;
    let (poly_A_vec_seq, poly_B_vec_seq, poly_C_vec_seq) = poly_vec_seq;

    //let (poly_A_vec_seq, poly_B_vec_seq, poly_C_vec_seq) = poly_vec_seq;
    let mut e = *claim;
    let mut r: Vec<Scalar> = Vec::new();
    let mut cubic_polys: Vec<CompressedUniPoly> = Vec::new();

    for _j in 0..num_rounds {
      let mut evals: Vec<(Scalar, Scalar, Scalar)> = Vec::new();

      for (poly_A, poly_B) in poly_A_vec_par.iter().zip(poly_B_vec_par.iter()) {
        let mut eval_point_0 = Scalar::zero();
        let mut eval_point_2 = Scalar::zero();
        let mut eval_point_3 = Scalar::zero();

        let len = poly_A.len() / 2;
        for i in 0..len {
          // eval 0: bound_func is A(low)
          eval_point_0 += comb_func(&poly_A[i], &poly_B[i], &poly_C_par[i]);

          // eval 2: bound_func is -A(low) + 2*A(high)
          let poly_A_bound_point = poly_A[len + i] + poly_A[len + i] - poly_A[i];
          let poly_B_bound_point = poly_B[len + i] + poly_B[len + i] - poly_B[i];
          let poly_C_bound_point = poly_C_par[len + i] + poly_C_par[len + i] - poly_C_par[i];
          eval_point_2 += comb_func(
            &poly_A_bound_point,
            &poly_B_bound_point,
            &poly_C_bound_point,
          );

          // eval 3: bound_func is -2A(low) + 3A(high); computed incrementally with bound_func applied to eval(2)
          let poly_A_bound_point = poly_A_bound_point + poly_A[len + i] - poly_A[i];
          let poly_B_bound_point = poly_B_bound_point + poly_B[len + i] - poly_B[i];
          let poly_C_bound_point = poly_C_bound_point + poly_C_par[len + i] - poly_C_par[i];

          eval_point_3 += comb_func(
            &poly_A_bound_point,
            &poly_B_bound_point,
            &poly_C_bound_point,
          );
        }

        evals.push((eval_point_0, eval_point_2, eval_point_3));
      }

      for (poly_A, poly_B, poly_C) in izip!(
        poly_A_vec_seq.iter(),
        poly_B_vec_seq.iter(),
        poly_C_vec_seq.iter()
      ) {
        let mut eval_point_0 = Scalar::zero();
        let mut eval_point_2 = Scalar::zero();
        let mut eval_point_3 = Scalar::zero();
        let len = poly_A.len() / 2;
        for i in 0..len {
          // eval 0: bound_func is A(low)
          eval_point_0 += comb_func(&poly_A[i], &poly_B[i], &poly_C[i]);
          // eval 2: bound_func is -A(low) + 2*A(high)
          let poly_A_bound_point = poly_A[len + i] + poly_A[len + i] - poly_A[i];
          let poly_B_bound_point = poly_B[len + i] + poly_B[len + i] - poly_B[i];
          let poly_C_bound_point = poly_C[len + i] + poly_C[len + i] - poly_C[i];
          eval_point_2 += comb_func(
            &poly_A_bound_point,
            &poly_B_bound_point,
            &poly_C_bound_point,
          );
          // eval 3: bound_func is -2A(low) + 3A(high); computed incrementally with bound_func applied to eval(2)
          let poly_A_bound_point = poly_A_bound_point + poly_A[len + i] - poly_A[i];
          let poly_B_bound_point = poly_B_bound_point + poly_B[len + i] - poly_B[i];
          let poly_C_bound_point = poly_C_bound_point + poly_C[len + i] - poly_C[i];
          eval_point_3 += comb_func(
            &poly_A_bound_point,
            &poly_B_bound_point,
            &poly_C_bound_point,
          );
        }
        evals.push((eval_point_0, eval_point_2, eval_point_3));
      }

      let evals_combined_0 = (0..evals.len()).map(|i| evals[i].0 * coeffs[i]).sum();
      let evals_combined_2 = (0..evals.len()).map(|i| evals[i].1 * coeffs[i]).sum();
      let evals_combined_3 = (0..evals.len()).map(|i| evals[i].2 * coeffs[i]).sum();

      let evals = vec![
        evals_combined_0,
        e - evals_combined_0,
        evals_combined_2,
        evals_combined_3,
      ];
      let poly = UniPoly::from_evals(&evals);

      // append the prover's message to the transcript
      poly.append_to_transcript(b"poly", transcript);

      //derive the verifier's challenge for the next round
      let r_j = transcript.challenge_scalar(b"challenge_nextround");
      r.push(r_j);

      // bound all tables to the verifier's challenege
      for (poly_A, poly_B) in poly_A_vec_par.iter_mut().zip(poly_B_vec_par.iter_mut()) {
        poly_A.bound_poly_var_top(&r_j);
        poly_B.bound_poly_var_top(&r_j);
      }
      poly_C_par.bound_poly_var_top(&r_j);

      for (poly_A, poly_B, poly_C) in izip!(
        poly_A_vec_seq.iter_mut(),
        poly_B_vec_seq.iter_mut(),
        poly_C_vec_seq.iter_mut()
      ) {
        poly_A.bound_poly_var_top(&r_j);
        poly_B.bound_poly_var_top(&r_j);
        poly_C.bound_poly_var_top(&r_j);
      }

      e = poly.evaluate(&r_j);
      cubic_polys.push(poly.compress());
    }

    let poly_A_par_final = (0..poly_A_vec_par.len())
      .map(|i| poly_A_vec_par[i][0])
      .collect();
    let poly_B_par_final = (0..poly_B_vec_par.len())
      .map(|i| poly_B_vec_par[i][0])
      .collect();
    let claims_prod = (poly_A_par_final, poly_B_par_final, poly_C_par[0]);

    let poly_A_seq_final = (0..poly_A_vec_seq.len())
      .map(|i| poly_A_vec_seq[i][0])
      .collect();
    let poly_B_seq_final = (0..poly_B_vec_seq.len())
      .map(|i| poly_B_vec_seq[i][0])
      .collect();
    let poly_C_seq_final = (0..poly_C_vec_seq.len())
      .map(|i| poly_C_vec_seq[i][0])
      .collect();
    let claims_dotp = (poly_A_seq_final, poly_B_seq_final, poly_C_seq_final);

    (
      SumcheckInstanceProof::new(cubic_polys),
      r,
      claims_prod,
      claims_dotp,
    )
  }
}

impl ZKSumcheckInstanceProof {
  pub fn prove_quad<F>(
    claim: &Scalar,
    blind_claim: &Scalar,
    num_rounds: usize,
    poly_A: &mut DensePolynomial,
    poly_B: &mut DensePolynomial,
    comb_func: F,
    gens_1: &MultiCommitGens,
    gens_n: &MultiCommitGens,
    transcript: &mut Transcript,
    random_tape: &mut RandomTape,
  ) -> (Self, Vec<Scalar>, Vec<Scalar>, Scalar)
  where
    F: Fn(&Scalar, &Scalar) -> Scalar,
  {
    let (blinds_poly, blinds_evals) = (
      random_tape.random_vector(b"blinds_poly", num_rounds),
      random_tape.random_vector(b"blinds_evals", num_rounds),
    );
    let mut claim_per_round = *claim;
    let mut comm_claim_per_round = claim_per_round.commit(blind_claim, gens_1).compress();

    let mut r: Vec<Scalar> = Vec::new();
    let mut comm_polys: Vec<CompressedGroup> = Vec::new();
    let mut comm_evals: Vec<CompressedGroup> = Vec::new();
    let mut proofs: Vec<DotProductProof> = Vec::new();

    for j in 0..num_rounds {
      let (poly, comm_poly) = {
        let mut eval_point_0 = Scalar::zero();
        let mut eval_point_2 = Scalar::zero();

        let len = poly_A.len() / 2;
        for i in 0..len {
          // eval 0: bound_func is A(low)
          eval_point_0 += comb_func(&poly_A[i], &poly_B[i]);

          // eval 2: bound_func is -A(low) + 2*A(high)
          let poly_A_bound_point = poly_A[len + i] + poly_A[len + i] - poly_A[i];
          let poly_B_bound_point = poly_B[len + i] + poly_B[len + i] - poly_B[i];
          eval_point_2 += comb_func(&poly_A_bound_point, &poly_B_bound_point);
        }

        let evals = vec![eval_point_0, claim_per_round - eval_point_0, eval_point_2];
        let poly = UniPoly::from_evals(&evals);
        let comm_poly = poly.commit(gens_n, &blinds_poly[j]).compress();
        (poly, comm_poly)
      };

      // append the prover's message to the transcript
      comm_poly.append_to_transcript(b"comm_poly", transcript);
      comm_polys.push(comm_poly);

      //derive the verifier's challenge for the next round
      let r_j = transcript.challenge_scalar(b"challenge_nextround");

      // bound all tables to the verifier's challenege
      poly_A.bound_poly_var_top(&r_j);
      poly_B.bound_poly_var_top(&r_j);

      // produce a proof of sum-check and of evaluation
      let (proof, claim_next_round, comm_claim_next_round) = {
        let eval = poly.evaluate(&r_j);
        let comm_eval = eval.commit(&blinds_evals[j], gens_1).compress();

        // we need to prove the following under homomorphic commitments:
        // (1) poly(0) + poly(1) = claim_per_round
        // (2) poly(r_j) = eval

        // Our technique is to leverage dot product proofs:
        // (1) we can prove: <poly_in_coeffs_form, (2, 1, 1, 1)> = claim_per_round
        // (2) we can prove: <poly_in_coeffs_form, (1, r_j, r^2_j, ..) = eval
        // for efficiency we batch them using random weights

        // add two claims to transcript
        comm_claim_per_round.append_to_transcript(b"comm_claim_per_round", transcript);
        comm_eval.append_to_transcript(b"comm_eval", transcript);

        // produce two weights
        let w = transcript.challenge_vector(b"combine_two_claims_to_one", 2);

        // compute a weighted sum of the RHS
        let target = w[0] * claim_per_round + w[1] * eval;
        let comm_target = GroupElement::vartime_multiscalar_mul(
          w.iter(),
          iter::once(&comm_claim_per_round)
            .chain(iter::once(&comm_eval))
            .map(|pt| pt.decompress().unwrap())
            .collect::<Vec<GroupElement>>(),
        )
        .compress();

        let blind = {
          let blind_sc = if j == 0 {
            blind_claim
          } else {
            &blinds_evals[j - 1]
          };

          let blind_eval = &blinds_evals[j];

          w[0] * blind_sc + w[1] * blind_eval
        };
        assert_eq!(target.commit(&blind, gens_1).compress(), comm_target);

        let a = {
          // the vector to use to decommit for sum-check test
          let a_sc = {
            let mut a = vec![Scalar::one(); poly.degree() + 1];
            a[0] += Scalar::one();
            a
          };

          // the vector to use to decommit for evaluation
          let a_eval = {
            let mut a = vec![Scalar::one(); poly.degree() + 1];
            for j in 1..a.len() {
              a[j] = a[j - 1] * r_j;
            }
            a
          };

          // take weighted sum of the two vectors using w
          assert_eq!(a_sc.len(), a_eval.len());
          (0..a_sc.len())
            .map(|i| w[0] * a_sc[i] + w[1] * a_eval[i])
            .collect::<Vec<Scalar>>()
        };

        let (proof, _comm_poly, _comm_sc_eval) = DotProductProof::prove(
          gens_1,
          gens_n,
          transcript,
          random_tape,
          &poly.as_vec(),
          &blinds_poly[j],
          &a,
          &target,
          &blind,
        );

        (proof, eval, comm_eval)
      };

      claim_per_round = claim_next_round;
      comm_claim_per_round = comm_claim_next_round;

      proofs.push(proof);
      r.push(r_j);
      comm_evals.push(comm_claim_per_round);
    }

    (
      ZKSumcheckInstanceProof::new(comm_polys, comm_evals, proofs),
      r,
      vec![poly_A[0], poly_B[0]],
      blinds_evals[num_rounds - 1],
    )
  }

  // zk sumcheck protocol involving 4 MLEs
  pub fn prove_cubic_with_additive_term<F>(
    claim: &Scalar,
    blind_claim: &Scalar,
    num_rounds: usize,
    poly_A: &mut DensePolynomial,
    poly_B: &mut DensePolynomial,
    poly_C: &mut DensePolynomial,
    poly_D: &mut DensePolynomial,
    comb_func: F,
    gens_1: &MultiCommitGens,
    gens_n: &MultiCommitGens,
    transcript: &mut Transcript,
    random_tape: &mut RandomTape,
  ) -> (Self, Vec<Scalar>, Vec<Scalar>, Scalar)
  where
    F: Fn(&Scalar, &Scalar, &Scalar, &Scalar) -> Scalar,
  {
    let (blinds_poly, blinds_evals) = (
      random_tape.random_vector(b"blinds_poly", num_rounds),
      random_tape.random_vector(b"blinds_evals", num_rounds),
    );

    let mut claim_per_round = *claim;
    let mut comm_claim_per_round = claim_per_round.commit(blind_claim, gens_1).compress();

    let mut r: Vec<Scalar> = Vec::new();
    let mut comm_polys: Vec<CompressedGroup> = Vec::new();
    let mut comm_evals: Vec<CompressedGroup> = Vec::new();
    let mut proofs: Vec<DotProductProof> = Vec::new();

    // kunxian: DensePolynomial/MLE is stored using little-endian layout: p[i1,...,in] = p.Z[int_from_le(i1...in)]
    for j in 0..num_rounds {
      let (poly, comm_poly) = {
        let mut eval_point_0 = Scalar::zero();
        let mut eval_point_2 = Scalar::zero();
        let mut eval_point_3 = Scalar::zero();

        // sumcheck protocol
        // at round j, computes a univariate polynomial 
        //    H_i(x) = \sum_b A(b, x, r) * (B(b, x, r)*C(b, x, r) - D(b, x, r))
        // where x.len() = 1, r.len() = j, b.len() = n - j - 1
        // 
        // sends < H_i(0), H_i(2), H_i(3) > to verifier
        //
        // receives a random challenge r_x from verifier
        // then for each M(b, x, r) computes the evaluations M(b, r_x, r) over boolean hypercube.
        //
        // the next round's expected sum becomes H_i(r_{n-i})


        // zk sumcheck protocol
        // at round 0, the expected sum is hidden to the verifier, the verifier only knows a hiding commitment to it.
        //
        // at round j, the prover cannot send H_i(X) directly to verifier, but instead sends a commitment to H_i(X).
        // 
        // in order to allow the verifier to check H_i(0) + H_i(1) = s_i only given 
        //     c_H = commit(H_i(X), blind_poly_i) = msm([h0, h1, h2, h3, blind_poly_i], G)
        //     c_s_i = commit(s_i, blind_i) = msm([s_i, blind_i], G)
        //
        //  argument of knowledge of [h0, h1, h2, h3, blind_poly_i], [s_i, blind_i], [s_{i+1}, blind_{i+1}] s.t.
        //  1. dotproduct([h0, h1, h2, h3, blind_poly_i], G) = c_H
        //  2. dotproduct([s_i, blind_i], G') = c_s_i
        //  3. <[h0, h1, h2, h3], [2, 1, 1, 1]> = s_i
        //  4. <[h0, h1, h2, h3], [1, r, r^2, r^3]> = s_{i+1}

        let len = poly_A.len() / 2;
        for i in 0..len {
          // eval 0: bound_func is A(low)
          eval_point_0 += comb_func(&poly_A[i], &poly_B[i], &poly_C[i], &poly_D[i]);
          
          // note that M(b, x, r) = eq(x, 0)*M(b, 0, r) + eq(x, 1)*M(b, 1, r)
          //                      = (1-x)*M(b, 0, r) + x*M(b, 1, r)
          //                      = M(b, 0, r) + x*(M(b, 1, r) - M(b, 0, r))

          // eval 2: bound_func is -A(low) + 2*A(high)
          let poly_A_bound_point = poly_A[len + i] + poly_A[len + i] - poly_A[i];
          let poly_B_bound_point = poly_B[len + i] + poly_B[len + i] - poly_B[i];
          let poly_C_bound_point = poly_C[len + i] + poly_C[len + i] - poly_C[i];
          let poly_D_bound_point = poly_D[len + i] + poly_D[len + i] - poly_D[i];
          eval_point_2 += comb_func(
            &poly_A_bound_point,
            &poly_B_bound_point,
            &poly_C_bound_point,
            &poly_D_bound_point,
          );

          // eval 3: bound_func is -2A(low) + 3A(high); computed incrementally with bound_func applied to eval(2)
          let poly_A_bound_point = poly_A_bound_point + poly_A[len + i] - poly_A[i];
          let poly_B_bound_point = poly_B_bound_point + poly_B[len + i] - poly_B[i];
          let poly_C_bound_point = poly_C_bound_point + poly_C[len + i] - poly_C[i];
          let poly_D_bound_point = poly_D_bound_point + poly_D[len + i] - poly_D[i];
          eval_point_3 += comb_func(
            &poly_A_bound_point,
            &poly_B_bound_point,
            &poly_C_bound_point,
            &poly_D_bound_point,
          );
        }

        let evals = vec![
          eval_point_0,
          claim_per_round - eval_point_0,
          eval_point_2,
          eval_point_3,
        ];
        let poly = UniPoly::from_evals(&evals);
        // kunxian: commit to a uni-variate polynomial of degree 3
        let comm_poly = poly.commit(gens_n, &blinds_poly[j]).compress();
        (poly, comm_poly)
      };

      // kunxian: in each round of the zk sumcheck protocol, prover sends a commitment to the uni-variate poly to verifier

      // append the prover's message to the transcript
      comm_poly.append_to_transcript(b"comm_poly", transcript);
      comm_polys.push(comm_poly);

      //derive the verifier's challenge for the next round
      let r_j = transcript.challenge_scalar(b"challenge_nextround");

      // bound all tables to the verifier's challenege
      poly_A.bound_poly_var_top(&r_j);
      poly_B.bound_poly_var_top(&r_j);
      poly_C.bound_poly_var_top(&r_j);
      poly_D.bound_poly_var_top(&r_j);

      // produce a proof of sum-check and of evaluation
      let (proof, claim_next_round, comm_claim_next_round) = {
        let eval = poly.evaluate(&r_j);
        let comm_eval = eval.commit(&blinds_evals[j], gens_1).compress();

        // we need to prove the following under homomorphic commitments:
        // (1) poly(0) + poly(1) = claim_per_round
        // (2) poly(r_j) = eval

        // Our technique is to leverage dot product proofs:
        // (1) we can prove: <poly_in_coeffs_form, (2, 1, 1, 1)> = claim_per_round
        // (2) we can prove: <poly_in_coeffs_form, (1, r_j, r^2_j, ..) = eval
        // for efficiency we batch them using random weights

        // add two claims to transcript
        comm_claim_per_round.append_to_transcript(b"comm_claim_per_round", transcript);
        comm_eval.append_to_transcript(b"comm_eval", transcript);

        // produce two weights
        let w = transcript.challenge_vector(b"combine_two_claims_to_one", 2);

        // compute a weighted sum of the RHS
        let target = w[0] * claim_per_round + w[1] * eval;
        let comm_target = GroupElement::vartime_multiscalar_mul(
          w.iter(),
          iter::once(&comm_claim_per_round)
            .chain(iter::once(&comm_eval))
            .map(|pt| pt.decompress().unwrap())
            .collect::<Vec<GroupElement>>(),
        )
        .compress();

        let blind = {
          let blind_sc = if j == 0 {
            blind_claim
          } else {
            &blinds_evals[j - 1]
          };

          let blind_eval = &blinds_evals[j];

          w[0] * blind_sc + w[1] * blind_eval
        };

        assert_eq!(target.commit(&blind, gens_1).compress(), comm_target);

        let a = {
          // the vector to use to decommit for sum-check test
          let a_sc = {
            let mut a = vec![Scalar::one(); poly.degree() + 1];
            a[0] += Scalar::one();
            a
          };

          // the vector to use to decommit for evaluation
          let a_eval = {
            let mut a = vec![Scalar::one(); poly.degree() + 1];
            for j in 1..a.len() {
              a[j] = a[j - 1] * r_j;
            }
            a
          };

          // take weighted sum of the two vectors using w
          assert_eq!(a_sc.len(), a_eval.len());
          (0..a_sc.len())
            .map(|i| w[0] * a_sc[i] + w[1] * a_eval[i])
            .collect::<Vec<Scalar>>()
        };

        let (proof, _comm_poly, _comm_sc_eval) = DotProductProof::prove(
          gens_1,
          gens_n,
          transcript,
          random_tape,
          &poly.as_vec(),
          &blinds_poly[j],
          &a,
          &target,
          &blind,
        );

        (proof, eval, comm_eval)
      };

      proofs.push(proof);
      claim_per_round = claim_next_round;
      comm_claim_per_round = comm_claim_next_round;
      r.push(r_j);
      comm_evals.push(comm_claim_per_round);
    }

    (
      ZKSumcheckInstanceProof::new(comm_polys, comm_evals, proofs),
      r,
      vec![poly_A[0], poly_B[0], poly_C[0], poly_D[0]],
      blinds_evals[num_rounds - 1],
    )
  }
}
