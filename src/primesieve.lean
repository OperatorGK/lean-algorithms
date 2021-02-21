import data.nat.prime
import tactic

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

lemma sieve_aux_mem (n: ℕ) (l: list ℕ) :
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

theorem sieve_keeps_primes₂ (m n: ℕ) :
  n < m -> nat.prime n -> n ∈ sieve m :=
begin  
  intros h₁ h₂,

  cases nat.le.dest h₂.left with n' h₃,  
  have h₄ : 2 ≤ m := by linarith,
  cases nat.le.dest h₄ with m' h₅,
  rw [←h₃, ←h₅] at *,
  clear h₃ h₄ h₅ m n,

  rw sieve,
  refine sieve_keeps_primes₁ _ _ h₂ _ _,
  
  simp only [list.mem_iff_nth_le, not_exists, add_lt_add_iff_left],
  intros i h₃,
  rw nth_le_drop_range,
  linarith,
  finish,

  rw list.mem_iff_nth_le,
  use n',
  fconstructor,
  finish,
  exact nth_le_drop_range _ _ _ (by linarith),
end

theorem prime_sieve (m n: ℕ) :
  n < m -> (nat.prime n ↔ n ∈ (sieve m)) :=
begin
  intro h,
  split,
  exact sieve_keeps_primes₂ m n h,

  sorry,
end

lemma sieve_filters₁ (n k: ℕ) (li: list ℕ) :
  (n ≠ k) -> (n ∣ k) -> k ∉ sieve_aux (n :: li) :=
begin
  intros h₁ h₂ h₃,
  safe [sieve_aux],
  replace h₃ := sieve_aux_mem k _ h₃,
  finish,
end

lemma sieve_sublist₁ (x: ℕ) (li: list ℕ) :
  sieve_aux li <+ sieve_aux (li ++ [x]) :=
begin
  apply well_founded.induction (measure_wf list.length) li,
  clear li,

  intros li h₁,

  cases li,
  simp only [sieve_aux, list.filter_nil, list.nil_append, list.sublist_cons],

  simp only [sieve_aux, list.filter_append, list.cons_append],
  apply list.sublist.cons2,
  
  by_cases li_hd ∣ x,
  finish,

  have h₂ : list.filter (λ (n : ℕ), ¬li_hd ∣ n) [x] = [x] := by finish,
  rw h₂,

  apply h₁,
  simp only [measure, inv_image, list.length],
  exact sieve_aux_wf _ li_tl,
end


lemma sieve_sublist₂ (li₁ li₂: list ℕ) :
  sieve_aux li₁ <+ sieve_aux (li₁ ++ li₂) :=
begin
  apply well_founded.induction (measure_wf list.length) li₂,
  intros x h₁,

  cases x,
  simp only [list.append_nil],

  have h₃ : x_hd :: x_tl ≠ list.nil := by simp only [ne.def, not_false_iff],
  rw [← list.init_append_last h₃, ← list.append_assoc],
  
  refine list.sublist.trans _ (sieve_sublist₁ _ _),
  apply h₁,
  
  simp only [measure, inv_image, list.length, nat.succ_pos',
    nat.add_succ_sub_one, add_zero, lt_add_iff_pos_right, list.length_init],
end

/-

theorem sieve_give_only_primes (n m: ℕ) :
  n < m → n ∈ sieve m → nat.prime n :=
begin
  intro h₁,
  intro h₂,
  rw sieve at h₂,
  split,
  cases n,
  have h₃: 0 ∉  list.drop 2 (list.range m),
  intro h₃,
  cases m,
  finish,
  cases m,
  finish,
  rw nat.succ_eq_add_one at h₃,
  rw nat.succ_eq_add_one at h₃,
  have h₄ : 1 + 1 = 2 := refl 2,
  rw add_assoc at h₃,
  rw h₄ at h₃,
  rw add_comm at h₃,
  rw list.mem_iff_nth_le at h₃,
  cases h₃,
  cases h₃_h,
  rw nth_le_drop_range at h₃_h_h,
  linarith,
  rw list.length_drop at h₃_h_w,
  rw list.length_range at h₃_h_w,
  rw add_comm at h₃_h_w,
  rw nat.add_sub_assoc at h₃_h_w,
  linarith,
  refl,
  have h₄ := sieve_aux_mem 0 (list.drop 2 (list.range m)) h₂,
  finish,
  cases n,
  have h₃: 1 ∉ list.drop 2 (list.range m),
  intro h₃,
  cases m,
  finish,
  cases m,
  finish,
  rw nat.succ_eq_add_one at h₃,
  rw nat.succ_eq_add_one at h₃,
  have h₄ : 1 + 1 = 2 := refl 2,
  rw add_assoc at h₃,
  rw h₄ at h₃,
  rw add_comm at h₃,
  rw list.mem_iff_nth_le at h₃,
   cases h₃,
  cases h₃_h,
  rw nth_le_drop_range at h₃_h_h,
  linarith,
  rw list.length_drop at h₃_h_w,
  rw list.length_range at h₃_h_w,
  rw add_comm at h₃_h_w,
  rw nat.add_sub_assoc at h₃_h_w,
  linarith,
  refl,
  have h₄ := sieve_aux_mem 1 (list.drop 2 (list.range m)) h₂,
  finish,
  have h₃ :=  zero_le n,
  exact nat.succ_le_succ (nat.succ_le_succ h₃),
  intro h₃,
  intro h₄,
  cases h₃,
  finish,  
  cases h₃,
  finish,
  right,
  
  
end


theorem sieve_filters_nonprimes₁ (n k: ℕ) (li: list ℕ):
  n > 1 -> n ∣ k -> n ≠ k -> k ∉ sieve_aux (n :: li) :=
begin
  intros h₁ h₂ h₃ h₄,
  
  cases n,
  linarith,
  cases n,
  linarith,
  rw sieve_aux at h₄,
  cases h₄,
  cc,
  
end
-/