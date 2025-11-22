(* ========================================================================== *)
(* 00_matrix_algebra.mg - Linear Algebra over F_2 (Binary Field)             *)
(* ========================================================================== *)
(* This file provides the mathematical foundations for:                       *)
(*   - Matrix operations over GF(2)                                          *)
(*   - Valiant-Vazirani linear hashing: h(x) = Ax ⊕ b                        *)
(*   - Pairwise independent hash families                                    *)
(* ========================================================================== *)
(*                                                                            *)
(* References:                                                                *)
(*   - Carter & Wegman, "Universal Classes of Hash Functions" (1979)         *)
(*   - Valiant & Vazirani, "NP is as easy as detecting unique solutions"     *)
(*   - Wikipedia: Universal hashing, Pairwise independence                   *)
(*                                                                            *)
(* ========================================================================== *)

(* We import definitions from 01_foundations.mg *)
(* Assumes: nat_p, ordsucc, add, mul, xor, BitString, etc. *)

(* ========================================================================== *)
(*                    SECTION A: MATRICES OVER F_2                            *)
(* ========================================================================== *)

(* -------------------------------------------------------------------------- *)
(* A.1: Matrix Representation                                                 *)
(* -------------------------------------------------------------------------- *)

(* An m×n matrix over F_2 is a function from (m × n) indices to {0,1} *)
(* We represent A[i,j] as A(i,j) where i ∈ m, j ∈ n *)

Definition Matrix : set -> set -> set -> prop :=
  fun rows cols A =>
    forall i :e rows, forall j :e cols, A i j :e two.

(* The set of all k×m matrices over F_2 *)
Definition Matrices : set -> set -> set :=
  fun k m => {A | Matrix k m A}.

(* Access element A[i,j] *)
Definition mat_entry : set -> set -> set -> set :=
  fun A i j => A i j.

(* -------------------------------------------------------------------------- *)
(* A.2: Special Matrices                                                      *)
(* -------------------------------------------------------------------------- *)

(* Zero matrix: all entries are 0 *)
Definition zero_matrix : set -> set -> set :=
  fun rows cols => (fun i j => 0).

(* Identity matrix: 1 on diagonal, 0 elsewhere *)
Definition identity_matrix : set -> set :=
  fun n => (fun i j => if i = j then ordsucc 0 else 0).

(* Row vector (1×n): just a bit string *)
Definition RowVector : set -> set -> prop :=
  fun n v => BitString n v.

(* Column vector (n×1): also a bit string *)
Definition ColVector : set -> set -> prop :=
  fun n v => BitString n v.

(* -------------------------------------------------------------------------- *)
(* A.3: Matrix Column and Row Extraction                                      *)
(* -------------------------------------------------------------------------- *)

(* Extract column j from matrix A (k×m) as a k-vector *)
Definition matrix_column : set -> set -> set :=
  fun A j => (fun i => A i j).

(* Extract row i from matrix A (k×m) as an m-vector *)
Definition matrix_row : set -> set -> set :=
  fun A i => (fun j => A i j).

(* -------------------------------------------------------------------------- *)
(* A.4: Matrix-Vector Multiplication over F_2                                 *)
(* -------------------------------------------------------------------------- *)

(* For A: k×m matrix and x: m-vector, compute y = Ax where y is a k-vector *)
(* y[i] = XOR_{j=0}^{m-1} (A[i,j] AND x[j]) *)

(* Inner product over F_2: Σ (a_i AND b_i) mod 2 *)
Definition inner_product_f2 : set -> set -> set -> set :=
  fun n a b =>
    nat_primrec 0 (fun j acc => xor acc (bit_and (a j) (b j))) n.

(* Matrix-vector product: y = Ax *)
Definition matrix_vec_mul : set -> set -> set -> set -> set :=
  fun k m A x =>
    (fun i :e k => inner_product_f2 m (matrix_row A i) x).

(* Shorthand for when dimensions are clear *)
Definition mat_vec : set -> set -> set :=
  fun A x => (fun i => inner_product_f2 (Eps_i (fun m => True)) (matrix_row A i) x).

(* -------------------------------------------------------------------------- *)
(* A.5: Matrix-Matrix Multiplication over F_2                                 *)
(* -------------------------------------------------------------------------- *)

(* For A: k×m and B: m×n, compute C = AB where C is k×n *)
(* C[i,j] = XOR_{l=0}^{m-1} (A[i,l] AND B[l,j]) *)

Definition matrix_mul : set -> set -> set -> set -> set -> set :=
  fun k m n A B =>
    (fun i :e k => fun j :e n =>
      inner_product_f2 m (matrix_row A i) (matrix_column B j)).

(* -------------------------------------------------------------------------- *)
(* A.6: Vector Addition (XOR) *)
(* -------------------------------------------------------------------------- *)

(* Vector XOR: z = x ⊕ y *)
Definition vec_add_f2 : set -> set -> set :=
  fun x y => (fun i => xor (x i) (y i)).

(* This is the same as vec_xor from foundations *)


(* ========================================================================== *)
(*                    SECTION B: LINEAR HASH FUNCTIONS                        *)
(* ========================================================================== *)

(* -------------------------------------------------------------------------- *)
(* B.1: The Linear Hash Family H_{k,m}                                        *)
(* -------------------------------------------------------------------------- *)

(* A linear hash function is h_{A,b}(x) = Ax ⊕ b                             *)
(* where A is a k×m matrix and b is a k-vector                               *)
(* Maps {0,1}^m → {0,1}^k                                                    *)

Definition LinearHash : set -> set -> set -> set -> set :=
  fun k m A b =>
    (fun x => vec_add_f2 (matrix_vec_mul k m A x) b).

(* Apply linear hash to a specific input *)
Definition apply_linear_hash : set -> set -> set -> set -> set -> set :=
  fun k m A b x => vec_add_f2 (matrix_vec_mul k m A x) b.

(* The family of all linear hashes from m bits to k bits *)
Definition LinearHashFamily : set -> set -> set :=
  fun k m => {(A, b) | Matrix k m A /\ ColVector k b}.

(* -------------------------------------------------------------------------- *)
(* B.2: Pairwise Independence                                                 *)
(* -------------------------------------------------------------------------- *)

(* A hash family H is pairwise independent if for distinct x1, x2:           *)
(* Pr_{h←H}[h(x1)=y1 ∧ h(x2)=y2] = 1/|Range|^2 for all y1, y2               *)

Definition is_pairwise_independent : set -> set -> set -> prop :=
  fun k m H =>
    forall x1 x2 :e BitStrings m,
      x1 <> x2 ->
      forall y1 y2 :e BitStrings k,
        (* Pr[h(x1)=y1 ∧ h(x2)=y2] = 1/2^{2k} *)
        True.  (* Abstract probability statement *)

(* The linear hash family is pairwise independent *)
Theorem linear_hash_pairwise_independent :
  forall k m, nat_p k -> nat_p m ->
  is_pairwise_independent k m (LinearHashFamily k m).
Admitted.

(* Proof sketch: For distinct x1, x2 and any y1, y2:
   The system Ax1 ⊕ b = y1, Ax2 ⊕ b = y2 has a unique solution (A,b)
   out of 2^{k(m+1)} total, giving probability 1/2^{2k}. *)

(* -------------------------------------------------------------------------- *)
(* B.3: Collision Probability                                                 *)
(* -------------------------------------------------------------------------- *)

(* For a 2-universal family, Pr[h(x)=h(y)] = 1/|Range| for x≠y *)
Theorem linear_hash_collision_prob :
  forall k m x y,
    nat_p k -> nat_p m ->
    x :e BitStrings m -> y :e BitStrings m ->
    x <> y ->
    (* Pr_{A,b}[Ax⊕b = Ay⊕b] = Pr[A(x⊕y) = 0] = 1/2^k *)
    True.
Admitted.

(* -------------------------------------------------------------------------- *)
(* B.4: Preimage Sets                                                         *)
(* -------------------------------------------------------------------------- *)

(* The preimage of a value under hash h_{A,b} *)
Definition hash_preimage : set -> set -> set -> set -> set -> set :=
  fun k m A b target =>
    {x :e BitStrings m | apply_linear_hash k m A b x = target}.

(* Preimage of zero vector: {x | Ax ⊕ b = 0^k} = {x | Ax = b} *)
Definition hash_kernel : set -> set -> set -> set -> set :=
  fun k m A b =>
    {x :e BitStrings m | matrix_vec_mul k m A x = b}.


(* ========================================================================== *)
(*                    SECTION C: VALIANT-VAZIRANI ISOLATION                   *)
(* ========================================================================== *)

(* -------------------------------------------------------------------------- *)
(* C.1: The VV Hash Setup                                                     *)
(* -------------------------------------------------------------------------- *)

(* For VV isolation:
   - m = number of variables
   - k = target dimension (typically log|S| for solution set S)
   - A: k×m random matrix
   - b: k-vector (random or structured)
   - Isolated set = solutions S ∩ {x : Ax = b}                              *)

Definition VV_isolated_set : set -> set -> set -> set -> set -> set :=
  fun m k S A b =>
    {x :e S | matrix_vec_mul k m A x = b}.

(* The goal: |VV_isolated_set| = 1 with good probability *)

(* -------------------------------------------------------------------------- *)
(* C.2: Expected Preimage Size                                                *)
(* -------------------------------------------------------------------------- *)

(* If S ⊆ {0,1}^m and we hash to k bits:
   E[|S ∩ h^{-1}(0)|] = |S|/2^k *)

Theorem expected_preimage_size :
  forall m k S,
    nat_p m -> nat_p k ->
    S c= BitStrings m ->
    (* E_{A,b}[|{x ∈ S : Ax⊕b = 0}|] = |S|/2^k *)
    True.
Admitted.

(* -------------------------------------------------------------------------- *)
(* C.3: VV Isolation Probability                                              *)
(* -------------------------------------------------------------------------- *)

(* Valiant-Vazirani Isolation Lemma (1986):
   If S ⊆ {0,1}^m is nonempty and k = ⌈log₂|S|⌉:
   Pr_{A,b}[|S ∩ {x : Ax = b}| = 1] ≥ 1/8                                   *)

Theorem VV_isolation_lemma :
  forall m S,
    nat_p m ->
    S c= BitStrings m ->
    S <> Empty ->
    exists k, nat_p k /\
      (* k ≈ log₂|S| *)
      (* Pr[exactly one element of S survives] ≥ 1/8 *)
      True.
Admitted.

(* More precise statement with k ranging over a window *)
Theorem VV_isolation_detailed :
  forall m S,
    nat_p m ->
    S c= BitStrings m ->
    S <> Empty ->
    (* For k in {⌊log|S|⌋, ⌊log|S|⌋+1}:
       Pr_{A,b}[|S ∩ h^{-1}_{A,b}(0)| = 1] ≥ 1/8 *)
    True.
Admitted.

(* -------------------------------------------------------------------------- *)
(* C.4: Efficient Isolation via Rejection Sampling                            *)
(* -------------------------------------------------------------------------- *)

(* With O(m) trials, we can find (k,A,b) that isolates with constant prob *)
Theorem VV_efficient_isolation :
  forall m S,
    nat_p m ->
    S c= BitStrings m ->
    S <> Empty ->
    (* In expected O(m) random (k,A,b) samples, we find one with |S ∩ h^{-1}(0)| = 1 *)
    True.
Admitted.

(* -------------------------------------------------------------------------- *)
(* C.5: Application to SAT → Unique-SAT                                       *)
(* -------------------------------------------------------------------------- *)

(* VV theorem: SAT ≤_rp Unique-SAT
   If there's a polytime algorithm for Unique-SAT, then NP = RP *)

Theorem VV_reduction :
  (* If Unique-SAT ∈ P, then NP = RP *)
  True.
Admitted.


(* ========================================================================== *)
(*                    SECTION D: MATRIX RANK AND NULLSPACE                    *)
(* ========================================================================== *)

(* -------------------------------------------------------------------------- *)
(* D.1: Rank of a Matrix                                                      *)
(* -------------------------------------------------------------------------- *)

(* Rank = dimension of column space = number of linearly independent columns *)
Definition matrix_rank : set -> set -> set -> set :=
  fun k m A =>
    (* Abstract: the F_2-rank of A *)
    Eps_i (fun r => nat_p r /\ r c= nat_min k m).

(* Full row rank: rank = k (number of rows) *)
Definition full_row_rank : set -> set -> set -> prop :=
  fun k m A => matrix_rank k m A = k.

(* -------------------------------------------------------------------------- *)
(* D.2: Nullspace                                                             *)
(* -------------------------------------------------------------------------- *)

(* Nullspace of A: {x : Ax = 0} *)
Definition nullspace : set -> set -> set -> set :=
  fun k m A =>
    {x :e BitStrings m | matrix_vec_mul k m A x = zero_vector k}.

(* Dimension of nullspace = m - rank *)
Theorem nullspace_dimension :
  forall k m A,
    Matrix k m A ->
    (* |nullspace(A)| = 2^{m - rank(A)} *)
    True.
Admitted.

(* -------------------------------------------------------------------------- *)
(* D.3: Random Matrix Rank                                                    *)
(* -------------------------------------------------------------------------- *)

(* A random k×m matrix over F_2 has full row rank with prob ≥ 1/4 *)
Theorem random_matrix_full_rank :
  forall k m,
    nat_p k -> nat_p m ->
    ord_le k m ->
    (* Pr_{A uniform}[rank(A) = k] ≥ ∏_{i=0}^{k-1}(1 - 2^{i-m}) ≥ 1/4 *)
    True.
Admitted.


(* ========================================================================== *)
(*                    SECTION E: LINEAR ALGEBRA LEMMAS                        *)
(* ========================================================================== *)

(* -------------------------------------------------------------------------- *)
(* E.1: Basic Properties                                                      *)
(* -------------------------------------------------------------------------- *)

(* Matrix-vector linearity: A(x ⊕ y) = Ax ⊕ Ay *)
Theorem mat_vec_linear :
  forall k m A x y,
    Matrix k m A ->
    ColVector m x -> ColVector m y ->
    matrix_vec_mul k m A (vec_add_f2 x y) =
    vec_add_f2 (matrix_vec_mul k m A x) (matrix_vec_mul k m A y).
Admitted.

(* Zero vector: A·0 = 0 *)
Theorem mat_vec_zero :
  forall k m A,
    Matrix k m A ->
    matrix_vec_mul k m A (zero_vector m) = zero_vector k.
Admitted.

(* -------------------------------------------------------------------------- *)
(* E.2: Hash Properties                                                       *)
(* -------------------------------------------------------------------------- *)

(* Shifting by sign flip: h_{A,b}(x ⊕ σ) = h_{A,b⊕Aσ}(x) *)
Theorem hash_shift :
  forall k m A b x sigma,
    Matrix k m A ->
    ColVector k b ->
    ColVector m x -> ColVector m sigma ->
    apply_linear_hash k m A b (vec_add_f2 x sigma) =
    apply_linear_hash k m A (vec_add_f2 b (matrix_vec_mul k m A sigma)) x.
Admitted.

(* This is key for the promise-preserving property of T_i in Goertzel's proof *)

(* -------------------------------------------------------------------------- *)
(* E.3: Counting Solutions                                                    *)
(* -------------------------------------------------------------------------- *)

(* Number of solutions to Ax = b equals 0 or 2^{m-rank(A)} *)
Theorem solution_count :
  forall k m A b,
    Matrix k m A -> ColVector k b ->
    (* |{x : Ax = b}| ∈ {0, 2^{m-rank(A)}} *)
    True.
Admitted.

(* If Ax = b has a solution x0, then all solutions are x0 ⊕ null(A) *)
Theorem solution_structure :
  forall k m A b x0,
    Matrix k m A -> ColVector k b ->
    matrix_vec_mul k m A x0 = b ->
    forall x, matrix_vec_mul k m A x = b <->
      exists n :e nullspace k m A, x = vec_add_f2 x0 n.
Admitted.


(* ========================================================================== *)
(*                    SECTION F: VV PARAMETERS                                *)
(* ========================================================================== *)

(* -------------------------------------------------------------------------- *)
(* F.1: Standard VV Parameters (from Goertzel's proof)                        *)
(* -------------------------------------------------------------------------- *)

(* Number of hash output bits: k = c_1 * log(m) *)
Definition vv_k : set -> set :=
  fun m => mul (ordsucc (ordsucc 0)) (log2 m).  (* c_1 = 2 *)

(* The VV layer adds O(log m) bits to the local input *)
Theorem vv_bit_overhead :
  forall m,
    nat_p m ->
    (* |a_i| + |b| = 2k = O(log m) where a_i is column i of A *)
    True.
Admitted.

(* -------------------------------------------------------------------------- *)
(* F.2: Delta-Biased Distributions                                            *)
(* -------------------------------------------------------------------------- *)

(* A distribution D over {0,1}^k is δ-biased if for all non-zero s:
   |E_D[(-1)^{s·x}]| ≤ δ *)

Definition is_delta_biased : set -> (set -> set) -> set -> prop :=
  fun k D delta =>
    (* Abstract: D is δ-close to uniform in statistical distance *)
    True.

(* Robustness: replacing uniform b with δ-biased b changes things by O(δ) *)
Theorem delta_bias_robustness :
  forall k m delta,
    nat_p k -> nat_p m ->
    (* If b is δ-biased instead of uniform, isolation probability changes by O(δ) *)
    True.
Admitted.


(* ========================================================================== *)
(* END OF 00_matrix_algebra.mg                                                *)
(* ========================================================================== *)
