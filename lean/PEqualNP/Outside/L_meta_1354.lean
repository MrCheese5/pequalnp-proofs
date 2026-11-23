import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1354

open PEqualNP.CircuitLowerBounds

def ins (n : ℕ) (W : List Bool) : List Bool := W.take n ++ false :: W.drop n

def mp (n L i : ℕ) : ℕ := if i < n then i else if i = n then n + L else i - 1

def tr (n L : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (mp n L)⟩

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem ins_length (n : ℕ) (W : List Bool) (h : n ≤ W.length) :
    (ins n W).length = W.length + 1 := by
  simp [ins, List.length_take, List.length_drop]; omega

theorem ins_getD (n L : ℕ) (W : List Bool) (h : n ≤ W.length) (hL : W.length ≤ n + L) (i : ℕ) :
    (ins n W).getD i false = W.getD (mp n L i) false := by
  unfold mp
  by_cases h1 : i < n
  · rw [if_pos h1]
    unfold ins
    rw [List.getD_append _ _ _ _ (by simp; omega)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_take, if_pos h1]
  · rw [if_neg h1]
    unfold ins
    rw [List.getD_append_right _ _ _ _ (by simp; omega)]
    have ht : (W.take n).length = n := by simp; omega
    rw [ht]
    by_cases h2 : i = n
    · subst h2
      rw [if_pos rfl, Nat.sub_self]
      simp only [List.getD_cons_zero]
      rw [List.getD_eq_default _ _ (by omega)]
    · rw [if_neg h2]
      have : i - n = (i - n - 1) + 1 := by omega
      rw [this, List.getD_cons_succ]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]
      congr 2
      omega

theorem ins_snoc (n : ℕ) (W : List Bool) (b : Bool) (h : n ≤ W.length) :
    ins n (W ++ [b]) = ins n W ++ [b] := by
  unfold ins
  rw [List.take_append_of_le_length h, List.drop_append_of_le_length h]
  simp

theorem fold_length (gs : List Gate) : ∀ W : List Bool,
    (gs.foldl stp W).length = W.length + gs.length := by
  induction gs with
  | nil => intro W; simp
  | cons g gs ih => intro W; simp only [List.foldl_cons, ih, stp]; simp; omega

theorem key (n L : ℕ) (gs : List Gate) : ∀ W : List Bool, n ≤ W.length →
    W.length + gs.length ≤ n + L →
    gs.foldl stp (ins n W) = ins n ((gs.map (tr n L)).foldl stp W) := by
  induction gs with
  | nil => intro W _ _; rfl
  | cons g gs ih =>
    intro W h1 h2
    simp only [List.foldl_cons, List.map_cons]
    have hstep : stp (ins n W) g = ins n (stp W (tr n L g)) := by
      unfold stp tr
      rw [ins_snoc n W _ h1]
      congr 3
      simp only [List.map_map]
      apply List.map_congr_left
      intro i _
      simp only [Function.comp]
      exact ins_getD n L W h1 (by simp at h2; omega) i
    rw [hstep]
    apply ih
    · unfold stp tr; simp; omega
    · unfold stp tr; simp at h2 ⊢; omega

end PEqualNP.Outside.L_meta_1354

theorem PEqualNP.Outside.L_meta_1354 : ∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate), ∃ gates' : List PEqualNP.CircuitLowerBounds.Gate, gates'.map PEqualNP.CircuitLowerBounds.Gate.op = gates.map PEqualNP.CircuitLowerBounds.Gate.op ∧ gates'.map (fun g => g.inputs.length) = gates.map (fun g => g.inputs.length) ∧ ∀ (j : ℕ) (x : Fin n → Bool), j < gates.length → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', n + j⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + 1 + j⟩ (List.ofFn x ++ [false]) := by
  intro n gates
  refine ⟨gates.map (PEqualNP.Outside.L_meta_1354.tr n gates.length), ?_, ?_, ?_⟩
  · simp [List.map_map, Function.comp_def, PEqualNP.Outside.L_meta_1354.tr]
  · simp [List.map_map, Function.comp_def, PEqualNP.Outside.L_meta_1354.tr]
  · intro j x hj
    have hx : List.ofFn x ++ [false] = PEqualNP.Outside.L_meta_1354.ins n (List.ofFn x) := by
      simp only [PEqualNP.Outside.L_meta_1354.ins]
      rw [List.take_of_length_le (by simp), List.drop_of_length_le (by simp)]
    have hk := PEqualNP.Outside.L_meta_1354.key n gates.length gates (List.ofFn x)
      (by simp) (by simp)
    show ((gates.map (PEqualNP.Outside.L_meta_1354.tr n gates.length)).foldl
        PEqualNP.Outside.L_meta_1354.stp (List.ofFn x)).getD (n + j) false =
      (gates.foldl PEqualNP.Outside.L_meta_1354.stp (List.ofFn x ++ [false])).getD (n + 1 + j) false
    have hlen := PEqualNP.Outside.L_meta_1354.fold_length
      (gates.map (PEqualNP.Outside.L_meta_1354.tr n gates.length)) (List.ofFn x)
    simp only [List.length_map, List.length_ofFn] at hlen
    rw [hx, hk, PEqualNP.Outside.L_meta_1354.ins_getD n gates.length _ (by omega) (by omega)]
    unfold PEqualNP.Outside.L_meta_1354.mp
    rw [if_neg (by omega), if_neg (by omega)]
    congr 1
    omega
