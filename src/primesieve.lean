import data.list
import data.nat.prime
import tactic
import tactic.gptf


lemma sieve_aux_wf (pred: ℕ -> Prop) [decidable_pred pred] (xs: list ℕ) :
  (xs.filter pred).length < xs.length + 1 := 
  by simp only [nat.lt_succ_of_le, list.length_le_of_sublist, list.filter_sublist]
  
def sieve_aux : list ℕ -> list ℕ
| [] := []
| (x :: xs) := 
  have (xs.filter $ λ n, ¬(x ∣ n)).length < xs.length + 1,
    from sieve_aux_wf _ _,
  x :: sieve_aux (xs.filter $ λ n, ¬(x ∣ n))
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf list.length⟩]}

def sieve (m: ℕ) : list ℕ := sieve_aux $ (list.range m).drop 2


lemma sieve_aux_sublist (l: list ℕ) :
  sieve_aux l <+ l :=
begin
  apply well_founded.induction (measure_wf list.length) l,
  intros x h₁,

  cases x,
  simp only [sieve_aux],
  
  simp only [sieve_aux],
  apply list.sublist.cons2,
    
  simp only [measure, inv_image, list.length] at h₁,
  generalize h₂ : list.filter (λ (n : ℕ), ¬x_hd ∣ n) x_tl = li',

  have h₃ : li' <+ x_tl := by simp only [←h₂, list.filter_sublist],
  have h₄ := h₁ li' (nat.lt_succ_iff.mpr (list.length_le_of_sublist h₃)),
  exact list.sublist.trans h₄ h₃,
end

lemma sieve_aux_mem {n: ℕ} {l: list ℕ} :
  n ∈ sieve_aux l -> n ∈ l := 
  by solve_by_elim [sieve_aux_sublist, list.sublist.subset]

theorem sieve_keeps_primes₁ (n: ℕ) (li: list ℕ):
  nat.prime n -> 1 ∉ li -> n ∈ li -> n ∈ (sieve_aux li) :=
begin
  intro h₁,
  apply well_founded.induction (measure_wf list.length) li,
  intro x,

  cases x,
  simp only [list.not_mem_nil, forall_prop_of_false, not_false_iff, forall_true_iff],
  
  replace h₁ := h₁.right x_hd,
  by_cases n = x_hd,
  finish [sieve_aux],

  intros h₂ h₃ h₄,
  right,

  apply h₂,
  all_goals { clear li h₂ },

  simp only [measure, inv_image, list.length, sieve_aux_wf],
  finish [list.mem_filter],
  finish [list.mem_filter],
end

lemma nth_le_drop_range (m n i: ℕ) (h: i < n):
  (list.drop m (list.range (m + n))).nth_le i (by simpa) = m + i :=
begin
  rw ← list.nth_le_drop (list.range (m + n)),
  rw list.nth_le_range,
  simpa only [list.length_range, add_lt_add_iff_left],
end

lemma range_drop_mem₁ (m n k: ℕ) :
  (k < n) -> k ∉ (list.range m).drop n :=
begin
  intro h₁,
  by_cases n ≤ m,

  cases nat.le.dest h with m' h₂,
  rw [←h₂] at *,
  clear h₂ m h,

  simp only [list.mem_iff_nth_le, not_exists, add_lt_add_iff_left],
  intros i h₂,
  rw nth_le_drop_range,
  linarith,
  simp only [*, list.length_drop, nat.add_sub_cancel_left, list.length_range] at *,

  set li := (list.range m).drop n with h₂,  
  have h₃: li.length = 0 := 
    by simp only [list.length_drop, list.length_range, le_of_not_ge h, nat.sub_eq_zero_of_le],

  simp only [list.length_eq_zero.mp h₃, list.not_mem_nil, not_false_iff],  
end

lemma range_drop_mem₂ (m n k: ℕ) :
  (k ≥ n) -> (k < m) -> k ∈ (list.range m).drop n :=
begin
  intros h₁ h₂,

  have h₄ : n ≤ m := by linarith,  
  cases nat.le.dest h₁ with k' h₃,  
  cases nat.le.dest h₄ with m' h₅,
  simp only [←h₃, ←h₅, add_lt_add_iff_left] at *,
  clear h₁ h₃ h₄ h₅ m k,

  simp only [list.mem_iff_nth_le],
  use k',

  fconstructor,
  simp only [*, list.length_drop, nat.add_sub_cancel_left, list.length_range],  

  rwa [nth_le_drop_range],
end

lemma range_drop_mem₃ (m n k: ℕ) :
  (k ≥ m) -> k ∉ (list.range m).drop n :=
begin
  intros h₁ h₂,
  have h₃ : k ∉ list.range m := by finish,
  have h₄ : k ∈ list.range m := list.mem_of_mem_drop h₂,
  contradiction,
end

theorem sieve_keeps_primes₂ (m n: ℕ) :
  n < m -> nat.prime n -> n ∈ sieve m :=
begin  
  intros h₁ h₂,
  refine sieve_keeps_primes₁ _ _ h₂ _ _,
  simp only [range_drop_mem₁, nat.one_lt_bit0_iff, not_false_iff],
  finish [nat.prime, range_drop_mem₂],
end

lemma sieve_filters₁ (n k: ℕ) (li: list ℕ) :
  (n ≠ k) -> (n ∣ k) -> k ∉ sieve_aux (n :: li) :=
begin
  intros h₁ h₂ h₃,
  safe [sieve_aux],
  replace h₃ := sieve_aux_mem h₃,
  finish,
end

lemma sieve_sublist₁ (x: ℕ) (li: list ℕ) :
  sieve_aux (li ++ [x]) <+ sieve_aux li ++ [x] :=
begin
  apply well_founded.induction (measure_wf list.length) li,
  clear li,

  intros li h₁,

  cases li,
  simp only [sieve_aux, list.filter_nil, list.nil_append],

  simp only [sieve_aux, list.filter_append, list.cons_append],
  apply list.sublist.cons2,

  by_cases li_hd ∣ x,

  have h₂ : list.filter (λ (n : ℕ), ¬li_hd ∣ n) [x] = list.nil := by finish,
  rw h₂,
  simp only [list.sublist_append_left, list.append_nil],

  have h₂ : list.filter (λ (n : ℕ), ¬li_hd ∣ n) [x] = [x] := by finish,
  rw h₂,
  apply h₁,
  
  simp only [measure, inv_image, list.length, sieve_aux_wf],
end

lemma sieve_filters₂ (n k: ℕ) (li: list ℕ) :
  (nat.prime n) -> (n ≠ k) -> (n ∣ k) -> 
  (1 ∉ li) -> (k ∉ li) -> (n ∈ li) -> (k ∉ sieve_aux (li ++ [k])) :=
begin
  intros h₀ h₁ h₂,
  apply well_founded.induction (measure_wf list.length) li,
  intros li' h₆ h₃ h₄ h₅,
  clear li,

  cases li',
  solve_by_elim,

  simp only [list.cons_append, sieve_aux, list.filter_append, list.mem_cons_iff, ne.def] at *,
  push_neg,
  split,
  tauto,

  by_cases li'_hd ∣ k,
  
  clear h₆,
  simp only [*, list.filter_cons_of_neg, list.filter_nil,
    list.append_nil, not_true, not_false_iff] at *,
  intro h₆,
  replace h₆ := sieve_aux_mem h₆,
  simp only [*, list.mem_filter, not_true] at *,
  
  simp only [*, list.filter_nil, not_false_iff, list.filter_cons_of_pos] at *,
  apply h₆,
  all_goals { clear h₆ },

  simp only [*, measure, inv_image, list.length, sieve_aux_wf],

  simp only [*, and_true, list.mem_filter, not_false_iff],
  tauto,

  simp only [*, list.mem_filter, and_true, not_false_iff],
  tauto,

  finish [list.mem_filter, nat.prime],
end

lemma range_drop_append (n k: ℕ):
  (k ≤ n) -> list.drop k (list.range (n + 1)) = list.drop k (list.range n) ++ [n] :=
begin
  intro h₁,
  cases nat.le.dest h₁ with n' h₂,
  rw [←h₂] at *,
  clear h₂ h₁ n,

  apply list.ext_le,
  simp only [list.length_append, list.length_drop, nat.add_sub_cancel_left,
    list.length_singleton, list.length_range],
  omega,
  
  intros i h₂ h₃,
  set li₂ := list.drop k (list.range (k + n')) ++ [k + n'],
  ring,
  rw nth_le_drop_range,

  by_cases i = n',
  
  have h₄ : i = li₂.length - 1,
  simpa only [nat.add_succ_sub_one, add_zero, list.length_append, list.length_drop, 
    nat.add_sub_cancel_left, list.length_singleton, list.length_range],

  simp only [h₄],
  rw ←list.last_eq_nth_le,
  simp only [nat.add_succ_sub_one, add_zero, list.length_append, list.length_drop,
    nat.add_sub_cancel_left, list.length_singleton, list.length_range, list.last_append],
  simp only [list.append_eq_nil, ne.def, not_false_iff, and_false],

  have h₄ : i < li₂.length - 1,
  simp only [*, nat.add_succ_sub_one, add_zero, list.length_append, list.length_drop, 
    nat.add_sub_cancel_left, list.length_singleton, list.length_range] at *,
  omega,

  rw [list.nth_le_append, nth_le_drop_range],

  finish,
  finish,
end

lemma sieve_filters₃ (n: ℕ) :
  ¬nat.prime n -> n ∉ sieve (n + 1) := 
begin
  intro h₁,
  rw sieve,
  
  cases n,
  exact dec_trivial,
  cases n,
  exact dec_trivial,

  rw nat.not_prime_iff_min_fac_lt at h₁,
  swap,
  exact dec_trivial,

  rw range_drop_append,
  swap,
  exact dec_trivial,

  set n' := n.succ.succ,
  set k := n'.min_fac,
  have h₂ := nat.min_fac_prime (dec_trivial : n' ≠ 1),
  refine sieve_filters₂ k n' _ _ _ _ _ _ _,

  exact h₂,
  linarith,
  exact nat.min_fac_dvd n',
  
  apply range_drop_mem₁,
  exact dec_trivial,

  apply range_drop_mem₃,
  simp only [ge_iff_le],

  apply range_drop_mem₂,
  exact h₂.left,
  exact h₁,
end

lemma sieve_filters_nonprimes (m n: ℕ) :
  n < m -> ¬nat.prime n -> n ∉ sieve m :=
begin
  intros h₁ h₂,

  induction m,
  exact dec_trivial,
  
  by_cases n = m_n,
  rw ←h,
  apply sieve_filters₃,
  exact h₂,

  have h₃ : n < m_n := by omega,
  specialize m_ih h₃,
  clear h h₁,

  by_cases 2 ≤ m_n,
  swap,
  
  cases m_n,
  exact dec_trivial,
  cases m_n,
  exact dec_trivial,
  simp only [nat.succ_eq_add_one, not_le] at *,
  linarith,

  rw [sieve, nat.succ_eq_add_one, range_drop_append],
  swap,
  exact h,

  intro h₁,
  have h₃ := sieve_sublist₁ m_n (list.drop 2 (list.range m_n)),
  rw [sieve] at m_ih,
  replace h₃ := (list.sublist.subset h₃) h₁,

  finish,
end

theorem prime_sieve (m n: ℕ) :
  n < m -> (nat.prime n ↔ n ∈ (sieve m)) :=
begin 
  intro h₁,
  split,
  exact sieve_keeps_primes₂ _ _ h₁,
  
  intro h₂,
  have h₃ := sieve_filters_nonprimes _ _ h₁,
  cc,
end
