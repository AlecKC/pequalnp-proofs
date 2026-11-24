import Mathlib
import PEqualNP.Defs


open PEqualNP.CircuitLowerBounds

private def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma getD_append_left (l1 l2 : List Bool) (i : ℕ) (hi : i < l1.length) :
    (l1 ++ l2).getD i false = l1.getD i false := by
  simp [List.getD, List.getElem?_append_left hi]

private lemma getD_append_self (l1 : List Bool) (b : Bool) :
    (l1 ++ [b]).getD l1.length false = b := by
  simp [List.getD]

private lemma getD_of_ge (l : List Bool) (i : ℕ) (hi : l.length ≤ i) :
    l.getD i false = false := by
  simp [List.getD, List.getElem?_eq_none hi]

private lemma getD_ofFn {n : ℕ} (z : Fin n → Bool) (i : ℕ) (hi : i < n) :
    (List.ofFn z).getD i false = z ⟨i, hi⟩ := by
  simp [List.getD, hi]

/-- The wire renumbering: permute the first ten input wires by `x2`, keep the
extra input wire and all gate wires, and send every later wire to 29 (which is
out of range, hence `false`, for a circuit of at most 18 gates on 11 inputs). -/
private def wireMap (x2 : Fin 10 → Fin 10) (L : ℕ) (u : ℕ) : ℕ :=
  if h : u < 10 then (x2 ⟨u, h⟩).val else if u < 11 + L then u else 29

private def gateMap (x2 : Fin 10 → Fin 10) (L : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wireMap x2 L)⟩

private lemma gateMap_inputs (x2 : Fin 10 → Fin 10) (L : ℕ) (g : Gate) :
    (gateMap x2 L g).inputs = g.inputs.map (wireMap x2 L) := rfl

private lemma wireMap_of_lt10 {x2 : Fin 10 → Fin 10} {L u : ℕ} (h : u < 10) :
    wireMap x2 L u = (x2 ⟨u, h⟩).val := by
  unfold wireMap
  rw [dif_pos h]

private lemma wireMap_of_mid {x2 : Fin 10 → Fin 10} {L u : ℕ}
    (h1 : 10 ≤ u) (h2 : u < 11 + L) : wireMap x2 L u = u := by
  unfold wireMap
  rw [dif_neg (show ¬ (u < 10) by omega), if_pos h2]

private lemma wireMap_of_big {x2 : Fin 10 → Fin 10} {L u : ℕ}
    (h : 11 + L ≤ u) : wireMap x2 L u = 29 := by
  unfold wireMap
  rw [dif_neg (show ¬ (u < 10) by omega), if_neg (show ¬ (u < 11 + L) by omega)]

private lemma wireMap_ten {x2 : Fin 10 → Fin 10} {L : ℕ} :
    wireMap x2 L 10 = 10 :=
  wireMap_of_mid (by omega) (by omega)

private lemma wireMap_lt10 {x2 : Fin 10 → Fin 10} {L u : ℕ} (h : u < 10) :
    wireMap x2 L u < 10 := by
  rw [wireMap_of_lt10 h]
  exact (x2 ⟨u, h⟩).isLt

private lemma wireMap_le29 {x2 : Fin 10 → Fin 10} {L u : ℕ} (hL : L ≤ 18) :
    wireMap x2 L u ≤ 29 := by
  by_cases h1 : u < 10
  · have h2 := wireMap_lt10 (x2 := x2) (L := L) h1
    omega
  · by_cases h2 : u < 11 + L
    · have h3 := wireMap_of_mid (x2 := x2) (L := L) (u := u) (by omega) h2
      omega
    · have h3 := wireMap_of_big (x2 := x2) (L := L) (u := u) (by omega)
      omega

/-- One step of the correspondence: if two wire lists agree under `wireMap`,
so do the lists after appending the same new wire value. -/
private lemma stepW_getD_correspond {x2 : Fin 10 → Fin 10} {L : ℕ} (hL : L ≤ 18)
    (w5 w1 : List Bool) (a : Bool) (n : ℕ)
    (hlen : w5.length = n) (hlen1 : w1.length = n) (hn : 11 ≤ n) (hnL : n < 11 + L)
    (hbase : ∀ u, w5.getD (wireMap x2 L u) false = w1.getD u false) :
    ∀ u, (w5 ++ [a]).getD (wireMap x2 L u) false = (w1 ++ [a]).getD u false := by
  have hn28 : n ≤ 28 := by omega
  have hA : ∀ u, n ≤ u → n ≤ wireMap x2 L u := by
    intro u hu
    by_cases h1 : u < 10
    · omega
    · by_cases h2 : u < 11 + L
      · rw [wireMap_of_mid (u := u) (by omega) h2]
        exact hu
      · rw [wireMap_of_big (u := u) (by omega)]
        omega
  have hF1 : ∀ u, wireMap x2 L u < n → u < n := by
    intro u hu
    rcases Nat.lt_or_ge u n with h | h
    · exact h
    · have h3 := hA u h
      omega
  have hF2 : ∀ u, wireMap x2 L u = n → u = n := by
    intro u hu
    rcases lt_trichotomy u n with h | h | h
    · have hlt : wireMap x2 L u < n := by
        by_cases h1 : u < 10
        · have h4 := wireMap_lt10 (x2 := x2) (L := L) h1
          omega
        · have h2 : u < 11 + L := by omega
          rw [wireMap_of_mid (u := u) (by omega) h2]
          exact h
      omega
    · exact h
    · have hne : wireMap x2 L u ≠ n := by
        by_cases h2 : u < 11 + L
        · rw [wireMap_of_mid (u := u) (by omega) h2]
          omega
        · rw [wireMap_of_big (u := u) (by omega)]
          omega
      exact absurd hu hne
  intro u
  rcases lt_trichotomy (wireMap x2 L u) n with h1 | h1 | h1
  · have hu : u < n := hF1 u h1
    rw [getD_append_left _ _ _ (by omega : wireMap x2 L u < w5.length),
      getD_append_left _ _ _ (by omega : u < w1.length)]
    exact hbase u
  · have hu : u = n := hF2 u h1
    have e1 : wireMap x2 L u = w5.length := by omega
    have e2 : u = w1.length := by omega
    rw [e1, getD_append_self, e2, getD_append_self]
  · have hleft : (w5 ++ [a]).getD (wireMap x2 L u) false = false := by
      apply getD_of_ge
      simp only [List.length_append, List.length_singleton]
      omega
    rw [hleft]
    rcases lt_trichotomy u n with h2 | h2 | h2
    · rw [getD_append_left _ _ _ (by omega : u < w1.length), ← hbase u,
        getD_of_ge _ _ (by omega : w5.length ≤ wireMap x2 L u)]
    · have hmid : wireMap x2 L u = u := wireMap_of_mid (u := u) (by omega) (by omega)
      exact absurd h1 (by omega)
    · rw [getD_of_ge _ _ (by
        simp only [List.length_append, List.length_singleton]
        omega : (w1 ++ [a]).length ≤ u)]

/-- The correspondence of wire values is preserved by folding the gate list:
at every stage, the value of wire `wireMap x2 L u` in the mapped circuit
equals the value of wire `u` in the original. -/
private lemma foldl_wires_correspond {x2 : Fin 10 → Fin 10} {L : ℕ} (hL : L ≤ 18) :
    ∀ (gs : List Gate) (w5 w1 : List Bool),
      w5.length = w1.length →
      w5.length + gs.length = 11 + L →
      11 ≤ w5.length →
      (∀ u, w5.getD (wireMap x2 L u) false = w1.getD u false) →
      ∀ u, ((gs.map (gateMap x2 L)).foldl stepW w5).getD (wireMap x2 L u) false
        = (gs.foldl stepW w1).getD u false := by
  intro gs
  induction gs with
  | nil =>
    intro w5 w1 _ _ _ hbase
    simpa using hbase
  | cons g gs ih =>
    intro w5 w1 hlen hsum hn hbase
    rw [List.length_cons] at hsum
    have hstep : (gateMap x2 L g).op.eval ((gateMap x2 L g).inputs.map fun i => w5.getD i false)
        = g.op.eval (g.inputs.map fun i => w1.getD i false) := by
      show g.op.eval ((g.inputs.map (wireMap x2 L)).map fun i => w5.getD i false) = _
      rw [List.map_map]
      have hfun : (fun i => w5.getD i false) ∘ wireMap x2 L
          = (fun i => w1.getD i false) := funext fun u => hbase u
      rw [hfun]
    have hstep5 : stepW w5 (gateMap x2 L g)
        = w5 ++ [g.op.eval (g.inputs.map fun i => w1.getD i false)] :=
      congrArg (fun v => w5 ++ [v]) hstep
    have hstep1 : stepW w1 g
        = w1 ++ [g.op.eval (g.inputs.map fun i => w1.getD i false)] := rfl
    have hbase' : ∀ u, (stepW w5 (gateMap x2 L g)).getD (wireMap x2 L u) false
        = (stepW w1 g).getD u false := by
      rw [hstep5, hstep1]
      exact stepW_getD_correspond hL w5 w1 _ w5.length rfl hlen.symm hn (by omega) hbase
    have hlen' : (stepW w5 (gateMap x2 L g)).length = (stepW w1 g).length := by
      simp [stepW, hlen]
    have hlen5 : (stepW w5 (gateMap x2 L g)).length = w5.length + 1 := by simp [stepW]
    have hsum' : (stepW w5 (gateMap x2 L g)).length + gs.length = 11 + L := by omega
    have hn' : 11 ≤ (stepW w5 (gateMap x2 L g)).length := by omega
    exact ih _ _ hlen' hsum' hn' hbase'

theorem PEqualNP.Outside.L_meta_4934 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (10 : ℕ) → Fin (10 : ℕ)), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x5 ∧ x5.size = x1.size ∧ x5.output ≤ (29 : ℕ) ∧ (∀ x6 ∈ x5.gates, ∀ x8 ∈ x6.inputs, x8 ≤ (29 : ℕ)) ∧ ∀ (x6 : Fin (10 : ℕ) → Bool) (x7 : Bool), x5.eval (List.ofFn x6 ++ [x7]) = x1.eval (List.ofFn (x6 ∘ x2) ++ [x7]) := by
  intro x1 x2 hF hsize
  have hL18 : x1.gates.length ≤ 18 := hsize
  refine ⟨⟨x1.gates.map (gateMap x2 x1.gates.length), wireMap x2 x1.gates.length x1.output⟩,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    exact ⟨(hF g' hg').1, by rw [gateMap_inputs, List.length_map]; exact (hF g' hg').2⟩
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
  · exact wireMap_le29 hL18
  · intro g hg w hw
    obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    obtain ⟨u, _, rfl⟩ := List.mem_map.mp hw
    exact wireMap_le29 hL18
  · intro x6 x7
    have e10 : ∀ (z : Fin 10 → Bool), (List.ofFn z ++ [x7]).getD 10 false = x7 := by
      intro z
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
      simp
    have hbase : ∀ u, (List.ofFn x6 ++ [x7]).getD (wireMap x2 x1.gates.length u) false
        = (List.ofFn (x6 ∘ x2) ++ [x7]).getD u false := by
      intro u
      by_cases h1 : u < 10
      · have hτ : wireMap x2 x1.gates.length u = (x2 ⟨u, h1⟩).val := wireMap_of_lt10 h1
        have hτ10 : wireMap x2 x1.gates.length u < 10 := wireMap_lt10 h1
        rw [getD_append_left _ _ _ (by simp only [List.length_ofFn]; exact hτ10),
          getD_append_left _ _ _ (by simp only [List.length_ofFn]; exact h1),
          getD_ofFn _ _ hτ10, getD_ofFn _ _ h1]
        simp only [Function.comp_apply]
        congr 1
        exact Fin.ext hτ
      · by_cases h2 : u = 10
        · subst h2
          rw [wireMap_ten, e10, e10]
        · by_cases h3 : u < 11 + x1.gates.length
          · rw [wireMap_of_mid (by omega) h3]
            have e1 : (List.ofFn x6 ++ [x7]).getD u false = false := by
              apply getD_of_ge
              simp only [List.length_append, List.length_ofFn, List.length_singleton]
              omega
            have e2 : (List.ofFn (x6 ∘ x2) ++ [x7]).getD u false = false := by
              apply getD_of_ge
              simp only [List.length_append, List.length_ofFn, List.length_singleton]
              omega
            rw [e1, e2]
          · rw [wireMap_of_big (by omega)]
            have e1 : (List.ofFn x6 ++ [x7]).getD 29 false = false := by
              apply getD_of_ge
              simp only [List.length_append, List.length_ofFn, List.length_singleton]
              omega
            have e2 : (List.ofFn (x6 ∘ x2) ++ [x7]).getD u false = false := by
              apply getD_of_ge
              simp only [List.length_append, List.length_ofFn, List.length_singleton]
              omega
            rw [e1, e2]
    have hcorr := foldl_wires_correspond (x2 := x2) (L := x1.gates.length) hL18
      x1.gates (List.ofFn x6 ++ [x7]) (List.ofFn (x6 ∘ x2) ++ [x7])
      (by simp) (by simp) (by simp) hbase x1.output
    show ((x1.gates.map (gateMap x2 x1.gates.length)).foldl stepW (List.ofFn x6 ++ [x7])).getD
        (wireMap x2 x1.gates.length x1.output) false
      = (x1.gates.foldl stepW (List.ofFn (x6 ∘ x2) ++ [x7])).getD x1.output false
    exact hcorr

