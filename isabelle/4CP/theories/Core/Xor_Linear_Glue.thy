theory Xor_Linear_Glue
  imports Main
begin

text \<open>Abstract XOR-space (just enough laws to reason about span and orthogonality).\<close>

locale xor_space =
  fixes zero :: 'x
  fixes xor  :: "'x => 'x => 'x"  (infixl "\<oplus>" 65)
  fixes dot  :: "'x => 'x => bool" (infixl "\<cdot>" 70)
  assumes xor_comm:    "x \<oplus> y = y \<oplus> x"
  and     xor_assoc:   "(x \<oplus> y) \<oplus> z = x \<oplus> (y \<oplus> z)"
  and     xor_zero:    "x \<oplus> zero = x"
  and     dot_add_left:  "(x \<oplus> y) \<cdot> z = ((x \<cdot> z) ~= (y \<cdot> z))"
  and     dot_add_right: "x \<cdot> (y \<oplus> z) = ((x \<cdot> y) ~= (x \<cdot> z))"
  and     dot_zero_left:  "zero \<cdot> z = False"
  and     dot_zero_right: "x \<cdot> zero = False"
begin

text \<open>XOR-span as inductive closure\<close>
inductive_set span :: "'x set => 'x set" for S where
  zero[intro]: "zero : span S"
| add[intro]:  "s : S ==> y : span S ==> (s \<oplus> y) : span S"

lemma span_mono:
  assumes "S <= T"
  shows "span S <= span T"
proof
  fix x assume "x : span S"
  then show "x : span T"
    by (induction rule: span.induct) (auto intro: span.intros assms subsetD)
qed

lemma orth_on_set_imp_orth_on_span:
  assumes ortS: "ALL g:S. z \<cdot> g = False"
  shows "ALL w:span S. z \<cdot> w = False"
proof
  fix w assume "w : span S"
  then show "z \<cdot> w = False"
  proof (induction rule: span.induct)
    case zero
    thus ?case by (simp add: dot_zero_right)
  next
    case (add s y)
    hence "z \<cdot> s = False" using ortS by blast
    moreover have "z \<cdot> y = False" using add.IH by simp
    ultimately show ?case by (simp add: dot_add_right)
  qed
qed

lemma orth_on_subset:
  assumes "S <= T" and "ALL g:T. z \<cdot> g = False" shows "ALL g:S. z \<cdot> g = False"
  using assms by blast

end

end
