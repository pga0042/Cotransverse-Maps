import CotransverseDimensionFour
import Mathlib.Tactic.FinCases

/-!
# The symmetric closure of the maximal nonsymmetric thick cube category

Lean 4.33.1 / mathlib v4.33.1 formalization of
`cotransverse_not_generated_by_transverse_and_symmetries.tex`.

The proof only uses three consequences of the characterization of
`widehat-square` in Proposition 2.13 of *Towards a theory of natural directed
paths*: its maps are cotransverse, its injective endomorphisms are identities,
and an injective restriction to an ordered two-face is again an ordered
coface.  `Transverse4` records these consequences in the rank-one/colour
form needed by the manuscript.  Thus the closure formalized
below is at least as large as the closure by the actual maps of
`widehat-square`; proving that `F` is absent from this larger closure proves
the claimed result.

The two general graph-theoretic results cited in the manuscript are not in
mathlib.  Their exact four-vertex instances are stated below as finite
propositions and proved by kernel reduction with `decide`; no axiom for
Gallai decomposition or threshold graphs is introduced.
-/

namespace CotransverseNotGeneratedByTransverseAndSymmetries

open Function
open CotransverseDimensionFour

abbrev RankOne4 := RankVertex 4 1
abbrev RankTwo4 := RankVertex 4 2

lemma DirectedEdge.subset {n : Nat} {A B : Cube n}
    (h : DirectedEdge A B) : A ⊆ B := by
  rcases h with ⟨i, hi, rfl⟩
  exact Finset.subset_insert i A

/-- Rank grows by the source rank, even when source and target dimensions
differ. -/
lemma hom_rank_eq_rank_empty_add {m n : Nat} (f : Cube m → Cube n)
    (hf : Cotransverse f) (A : Cube m) :
    (f A).card = (f ∅).card + A.card := by
  classical
  induction A using Finset.induction_on with
  | empty => simp
  | @insert i A hi ih =>
      have hedge : DirectedEdge A (insert i A) := ⟨i, hi, rfl⟩
      have himage := DirectedEdge.card_eq (hf hedge)
      rw [himage, ih]
      simp [hi, Nat.add_assoc]

/-- There is no cotransverse map from a larger-dimensional cube to a
smaller-dimensional cube. -/
theorem source_dimension_le_target {m n : Nat} (f : Cube m → Cube n)
    (hf : Cotransverse f) : m ≤ n := by
  have htop : (f (Finset.univ : Cube m)).card = (f ∅).card + m := by
    simpa using hom_rank_eq_rank_empty_add f hf (Finset.univ : Cube m)
  have htarget : (f (Finset.univ : Cube m)).card ≤ n := by
    simpa using Finset.card_le_univ (f (Finset.univ : Cube m))
  omega

theorem no_cotransverse_map_to_smaller {m n : Nat} (hmn : n < m) :
    ¬∃ f : Cube m → Cube n, Cotransverse f := by
  rintro ⟨f, hf⟩
  exact (Nat.not_le_of_lt hmn) (source_dimension_le_target f hf)

/-- Every intermediate cube in a cotransverse factorization from `[4]`
back to `[4]` again has dimension four. -/
theorem intermediate_dimension_eq_four {d : Nat}
    (hleft : ∃ f : Cube 4 → Cube d, Cotransverse f)
    (hright : ∃ g : Cube d → Cube 4, Cotransverse g) : d = 4 := by
  rcases hleft with ⟨f, hf⟩
  rcases hright with ⟨g, hg⟩
  have h4d : 4 ≤ d := source_dimension_le_target f hf
  have hd4 : d ≤ 4 := source_dimension_le_target g hg
  omega

/-- A cover-preserving map of Boolean cubes is monotone. -/
theorem cotransverse_monotone {m n : Nat} (f : Cube m → Cube n)
    (hf : Cotransverse f) {A B : Cube m} (hAB : A ⊆ B) : f A ⊆ f B := by
  classical
  by_cases hEq : A = B
  · simp [hEq]
  · have hss : A ⊂ B := (Finset.ssubset_iff_subset_ne).2 ⟨hAB, hEq⟩
    rcases Finset.ssubset_iff_exists_cons_subset.mp hss with ⟨i, hi, hiB⟩
    have hedge : DirectedEdge A (insert i A) := ⟨i, hi, rfl⟩
    have hiB' : insert i A ⊆ B := by
      simpa only [Finset.cons_eq_insert] using hiB
    exact (DirectedEdge.subset (hf hedge)).trans
      (cotransverse_monotone f hf hiB')
termination_by B.card - A.card
decreasing_by
  have hcard : A.card < B.card := Finset.card_lt_card hss
  simp [hi]
  omega

/-- The coordinate occupied by the image of the singleton `{i}`. -/
noncomputable def rankOneIndex (f : Cube 4 → Cube 4)
    (hf : Cotransverse f) (i : Fin 4) : Fin 4 :=
  Classical.choose (Finset.card_eq_one.mp (by
    simpa using rank_preservation f hf ({i} : Cube 4)))

lemma rankOneIndex_spec (f : Cube 4 → Cube 4) (hf : Cotransverse f)
    (i : Fin 4) : f {i} = {rankOneIndex f hf i} :=
  Classical.choose_spec (Finset.card_eq_one.mp (by
    simpa using rank_preservation f hf ({i} : Cube 4)))

lemma rankOneIndex_congr (f g : Cube 4 → Cube 4)
    (hf : Cotransverse f) (hg : Cotransverse g) (hfg : f = g) (i : Fin 4) :
    rankOneIndex f hf i = rankOneIndex g hg i := by
  have hsets : ({rankOneIndex f hf i} : Cube 4) = {rankOneIndex g hg i} := by
    rw [← rankOneIndex_spec f hf i, ← rankOneIndex_spec g hg i, hfg]
  simpa using hsets

lemma rankOneIndex_comp (f g : Cube 4 → Cube 4)
    (hf : Cotransverse f) (hg : Cotransverse g) (i : Fin 4) :
    rankOneIndex (g ∘ f) (hg.comp hf) i =
      rankOneIndex g hg (rankOneIndex f hf i) := by
  have hsets :
      ({rankOneIndex (g ∘ f) (hg.comp hf) i} : Cube 4) =
        {rankOneIndex g hg (rankOneIndex f hf i)} := by
    rw [← rankOneIndex_spec (g ∘ f) (hg.comp hf) i]
    simp only [Function.comp_apply]
    rw [rankOneIndex_spec f hf i, rankOneIndex_spec g hg]
  simpa using hsets

lemma rankOneIndex_perm (σ : Equiv.Perm (Fin 4)) (i : Fin 4) :
    rankOneIndex (permMap σ) (permMap_cotransverse σ) i = σ i := by
  have hsets :
      ({rankOneIndex (permMap σ) (permMap_cotransverse σ) i} : Cube 4) =
        {σ i} := by
    rw [← rankOneIndex_spec (permMap σ) (permMap_cotransverse σ) i]
    simp [permMap]
  simpa using hsets

lemma permMap_refl_four :
    permMap (Equiv.refl (Fin 4)) = (id : Cube 4 → Cube 4) := by
  funext A
  simp [permMap]

lemma permMap_comp_four (σ τ : Equiv.Perm (Fin 4)) :
    permMap σ ∘ permMap τ = permMap (τ.trans σ) := by
  funext A
  simp [permMap, Function.comp_apply, Finset.map_map]

/-! ## The consequences of the characterization of `widehat-square` -/

/-- The colour monotonicity forced by injective ordered two-face
restrictions. -/
def ColourMonotone (h : Cube 4 → Cube 4) : Prop :=
  ∀ ⦃i j k a x y z : Fin 4⦄,
    i < j → j < k →
    h {i} = {a} → h {j} = {a} → h {k} = {a} →
    h {i, j} = {a, x} → h {i, k} = {a, y} →
    h {j, k} = {a, z} → x ≤ y ∧ y ≤ z

/-- A deliberately weak interface containing every endomorphism of
`widehat-square([4],[4])`.  Using a larger class strengthens the final
non-generation theorem. -/
structure Transverse4 (h : Cube 4 → Cube 4) : Prop where
  cotransverse : Cotransverse h
  rankOne_injective_eq_id :
    Injective (rankOneIndex h cotransverse) → h = id
  colourMonotone : ColourMonotone h

/-! ## Words in transverse maps and coordinate permutations -/

inductive SymStep4 where
  | perm (σ : Equiv.Perm (Fin 4))
  | transverse (h : Cube 4 → Cube 4) (hh : Transverse4 h)

def SymStep4.eval : SymStep4 → Cube 4 → Cube 4
  | .perm σ => permMap σ
  | .transverse h _ => h

theorem SymStep4.cotransverse : (s : SymStep4) → Cotransverse s.eval
  | .perm σ => permMap_cotransverse σ
  | .transverse _ hh => hh.cotransverse

noncomputable def SymStep4.rankOne (s : SymStep4) : Fin 4 → Fin 4 :=
  rankOneIndex s.eval s.cotransverse

def evalSymWord : List SymStep4 → Cube 4 → Cube 4
  | [], A => A
  | s :: w, A => evalSymWord w (s.eval A)

def SymGenerated (f : Cube 4 → Cube 4) : Prop :=
  ∃ w : List SymStep4, evalSymWord w = f

lemma evalSymWord_append (u v : List SymStep4) :
    evalSymWord (u ++ v) = evalSymWord v ∘ evalSymWord u := by
  funext A
  induction u generalizing A with
  | nil => rfl
  | cons s u ih =>
      simp only [List.cons_append, evalSymWord, Function.comp_apply]
      exact ih (s.eval A)

lemma evalSymWord_cotransverse (w : List SymStep4) :
    Cotransverse (evalSymWord w) := by
  induction w with
  | nil =>
      intro A B hAB
      exact hAB
  | cons s w ih => exact ih.comp s.cotransverse

lemma rankOne_evalSymWord_cons (s : SymStep4) (w : List SymStep4)
    (i : Fin 4) :
    rankOneIndex (evalSymWord (s :: w)) (evalSymWord_cotransverse (s :: w)) i =
      rankOneIndex (evalSymWord w) (evalSymWord_cotransverse w) (s.rankOne i) := by
  change rankOneIndex (evalSymWord w ∘ s.eval) _ i = _
  simpa [evalSymWord, SymStep4.rankOne] using
    rankOneIndex_comp s.eval (evalSymWord w) s.cotransverse
      (evalSymWord_cotransverse w) i

lemma rankOne_evalSymWord_nil (i : Fin 4) :
    rankOneIndex (evalSymWord []) (evalSymWord_cotransverse []) i = i := by
  calc
    rankOneIndex (evalSymWord []) (evalSymWord_cotransverse []) i =
        rankOneIndex (permMap (Equiv.refl (Fin 4)))
          (permMap_cotransverse (Equiv.refl (Fin 4))) i := by
            apply rankOneIndex_congr
            exact permMap_refl_four.symm
    _ = i := by simpa using rankOneIndex_perm (Equiv.refl (Fin 4)) i

lemma first_noninjective_rankOne_factor (w : List SymStep4)
    (hbad : ¬Injective
      (rankOneIndex (evalSymWord w) (evalSymWord_cotransverse w))) :
    ∃ (pre : List SymStep4) (s : SymStep4) (post : List SymStep4),
      w = pre ++ s :: post ∧
      (∀ t ∈ pre, Injective t.rankOne) ∧ ¬Injective s.rankOne := by
  induction w with
  | nil =>
      exfalso
      apply hbad
      intro i j hij
      simpa [rankOne_evalSymWord_nil] using hij
  | cons s w ih =>
      by_cases hs : Injective s.rankOne
      · have htail : ¬Injective
            (rankOneIndex (evalSymWord w) (evalSymWord_cotransverse w)) := by
          intro hw
          apply hbad
          intro i j hij
          rw [rankOne_evalSymWord_cons, rankOne_evalSymWord_cons] at hij
          exact hs (hw hij)
        rcases ih htail with ⟨pre, t, post, hw, hpre, ht⟩
        refine ⟨s :: pre, t, post, ?_, ?_, ht⟩
        · simp [hw]
        · intro r hr
          simp only [List.mem_cons] at hr
          rcases hr with rfl | hr
          · exact hs
          · exact hpre r hr
      · exact ⟨[], s, w, rfl, by simp, hs⟩

lemma injective_step_is_permutation (s : SymStep4)
    (hs : Injective s.rankOne) :
    ∃ σ : Equiv.Perm (Fin 4), s.eval = permMap σ := by
  cases s with
  | perm σ => exact ⟨σ, rfl⟩
  | transverse h hh =>
      have hid : h = id := hh.rankOne_injective_eq_id (by
        simpa [SymStep4.rankOne, SymStep4.eval, SymStep4.cotransverse] using hs)
      refine ⟨Equiv.refl (Fin 4), ?_⟩
      exact hid.trans permMap_refl_four.symm

lemma injective_prefix_is_permutation (w : List SymStep4)
    (hw : ∀ s ∈ w, Injective s.rankOne) :
    ∃ σ : Equiv.Perm (Fin 4), evalSymWord w = permMap σ := by
  induction w with
  | nil => exact ⟨Equiv.refl (Fin 4), permMap_refl_four.symm⟩
  | cons s w ih =>
      have hs : Injective s.rankOne := hw s (by simp)
      have htail : ∀ t ∈ w, Injective t.rankOne := by
        intro t ht
        exact hw t (by simp [ht])
      rcases injective_step_is_permutation s hs with ⟨τ, hτ⟩
      rcases ih htail with ⟨σ, hσ⟩
      refine ⟨τ.trans σ, ?_⟩
      calc
        evalSymWord (s :: w) = evalSymWord w ∘ s.eval := rfl
        _ = permMap σ ∘ permMap τ := by rw [hσ, hτ]
        _ = permMap (τ.trans σ) := permMap_comp_four σ τ

lemma F_rankOne_not_injective :
    ¬Injective (rankOneIndex F F_cotransverse) := by
  intro hinjective
  have hsets : F ({(0 : Fin 4)} : Cube 4) = F {1} := by decide
  have hidx : rankOneIndex F F_cotransverse 0 =
      rankOneIndex F F_cotransverse 1 := by
    have hsingletons :
        ({rankOneIndex F F_cotransverse 0} : Cube 4) =
          {rankOneIndex F F_cotransverse 1} := by
      rw [← rankOneIndex_spec F F_cotransverse 0,
        ← rankOneIndex_spec F F_cotransverse 1]
      exact hsets
    simpa using hsingletons
  exact (by decide : (0 : Fin 4) ≠ 1) (hinjective hidx)

/-- The formal first-factor reduction in the proof of the main theorem. -/
theorem generated_has_first_transverse_factor (hgenerated : SymGenerated F) :
    ∃ (h g : Cube 4 → Cube 4) (σ : Equiv.Perm (Fin 4))
      (hh : Transverse4 h),
      ¬Injective (rankOneIndex h hh.cotransverse) ∧
        F = g ∘ h ∘ permMap σ := by
  rcases hgenerated with ⟨w, hw⟩
  have hbad : ¬Injective
      (rankOneIndex (evalSymWord w) (evalSymWord_cotransverse w)) := by
    intro hinjective
    apply F_rankOne_not_injective
    intro i j hij
    apply hinjective
    calc
      rankOneIndex (evalSymWord w) (evalSymWord_cotransverse w) i =
          rankOneIndex F F_cotransverse i :=
        rankOneIndex_congr _ _ _ _ hw i
      _ = rankOneIndex F F_cotransverse j := hij
      _ = rankOneIndex (evalSymWord w) (evalSymWord_cotransverse w) j :=
        (rankOneIndex_congr _ _ _ _ hw j).symm
  rcases first_noninjective_rankOne_factor w hbad with
    ⟨pre, s, post, hwdecomp, hpre, hs⟩
  rcases injective_prefix_is_permutation pre hpre with ⟨σ, hσ⟩
  cases s with
  | perm τ =>
      exfalso
      apply hs
      intro i j hij
      change rankOneIndex (permMap τ) (permMap_cotransverse τ) i =
        rankOneIndex (permMap τ) (permMap_cotransverse τ) j at hij
      rw [rankOneIndex_perm τ i, rankOneIndex_perm τ j] at hij
      exact τ.injective hij
  | transverse h hh =>
      refine ⟨h, evalSymWord post, σ, hh, ?_, ?_⟩
      · simpa [SymStep4.rankOne, SymStep4.eval, SymStep4.cotransverse] using hs
      · subst w
        rw [evalSymWord_append, hσ] at hw
        funext A
        exact congrFun hw.symm A

/-! ## Kernel refinement and the rank-one collapse -/

/-- The kernel partition of `u` refines that of `v`. -/
def KernelRefines (u v : Cube 4 → Cube 4) : Prop :=
  ∀ ⦃A B⦄, u A = u B → v A = v B

lemma kernelRefines_of_factor (u g : Cube 4 → Cube 4) :
    KernelRefines u (g ∘ u) := by
  intro A B hAB
  exact congrArg g hAB

lemma rankOneIndex_mem_image (u : Cube 4 → Cube 4)
    (hu : Cotransverse u) {i : Fin 4} {A : Cube 4} (hi : i ∈ A) :
    rankOneIndex u hu i ∈ u A := by
  have hsubset : ({i} : Cube 4) ⊆ A := by simpa using hi
  have himage := cotransverse_monotone u hu hsubset
  rw [rankOneIndex_spec u hu i] at himage
  exact himage (by simp)

/-- When two singleton images are different, monotonicity and rank
preservation determine the image of the pair. -/
lemma image_pair_of_distinct_rankOne (u : Cube 4 → Cube 4)
    (hu : Cotransverse u) {p q : Fin 4} (hpq : p ≠ q)
    (hdistinct : rankOneIndex u hu p ≠ rankOneIndex u hu q) :
    u {p, q} = {rankOneIndex u hu p, rankOneIndex u hu q} := by
  let ap := rankOneIndex u hu p
  let aq := rankOneIndex u hu q
  have hp : ap ∈ u {p, q} :=
    rankOneIndex_mem_image u hu (by simp [hpq])
  have hq : aq ∈ u {p, q} :=
    rankOneIndex_mem_image u hu (by simp)
  have hsub : ({ap, aq} : Cube 4) ⊆ u {p, q} := by
    simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using
      And.intro hp hq
  have hcardImage : (u {p, q}).card = 2 := by
    rw [rank_preservation u hu]
    simp [hpq]
  have hcardPair : ({ap, aq} : Cube 4).card = 2 := by
    simp [ap, aq, hdistinct]
  exact (Finset.Subset.antisymm
    (fun x hx => by
      by_contra hnot
      have hstrict : ({ap, aq} : Cube 4) ⊂ u {p, q} :=
        (Finset.ssubset_iff_subset_ne).2 ⟨hsub, by
          intro heq
          exact hnot (heq ▸ hx)⟩
      have := Finset.card_lt_card hstrict
      omega)
    hsub)

/-- A fibre of the rank-one map has the module property forced by the
factorization through `F`. -/
def FibreModuleCondition (a : Fin 4 → Fin 4) : Prop :=
  ∀ ⦃p q⦄, p ≠ q → a p = a q →
    ∀ k, a k ≠ a p →
      (PathAdjacent4 p k ↔ PathAdjacent4 q k)

lemma F_pair_equality_detects_adjacency {p q k : Fin 4}
    (hpk : p ≠ k) (hqk : q ≠ k)
    (heq : F {p, k} = F {q, k}) :
    PathAdjacent4 p k ↔ PathAdjacent4 q k := by
  by_cases hp : PathAdjacent4 p k <;>
    by_cases hq : PathAdjacent4 q k
  · exact ⟨fun _ => hq, fun _ => hp⟩
  · rw [F_on_pair hpk, F_on_pair hqk, if_pos hp, if_neg hq] at heq
    exact False.elim ((by decide :
      ({(0 : Fin 4), (1 : Fin 4)} : Cube 4) ≠ {0, 2}) heq)
  · rw [F_on_pair hpk, F_on_pair hqk, if_neg hp, if_pos hq] at heq
    exact False.elim ((by decide :
      ({(0 : Fin 4), (2 : Fin 4)} : Cube 4) ≠ {0, 1}) heq)
  · exact ⟨fun h => (hp h).elim, fun h => (hq h).elim⟩

lemma fibreModuleCondition_of_kernel (u : Cube 4 → Cube 4)
    (hu : Cotransverse u) (hkernel : KernelRefines u F) :
    FibreModuleCondition (rankOneIndex u hu) := by
  intro p q hpq hpqImage k hkImage
  have hkp : k ≠ p := by
    intro h
    subst k
    exact hkImage rfl
  have hkq : k ≠ q := by
    intro h
    subst k
    exact hkImage hpqImage.symm
  have hpkImage :
      u {p, k} = {rankOneIndex u hu p, rankOneIndex u hu k} :=
    image_pair_of_distinct_rankOne u hu hkp.symm (Ne.symm hkImage)
  have hqkImage :
      u {q, k} = {rankOneIndex u hu q, rankOneIndex u hu k} :=
    image_pair_of_distinct_rankOne u hu hkq.symm (by
      intro h
      apply hkImage
      exact h.symm.trans hpqImage.symm)
  apply F_pair_equality_detects_adjacency hkp.symm hkq.symm
  apply hkernel
  rw [hpkImage, hqkImage, hpqImage]

/-- A module of the concrete path graph `P₄`. -/
def PathModule4 (M : Cube 4) : Prop :=
  ∀ p, p ∈ M → ∀ q, q ∈ M → ∀ k, k ∉ M →
    (PathAdjacent4 p k ↔ PathAdjacent4 q k)

instance instDecidablePathModule4 (M : Cube 4) : Decidable (PathModule4 M) := by
  unfold PathModule4
  let byP : DecidablePred fun p : Fin 4 => p ∈ M →
      ∀ q, q ∈ M → ∀ k, k ∉ M →
        (PathAdjacent4 p k ↔ PathAdjacent4 q k) := fun p => by
    let byQ : DecidablePred fun q : Fin 4 => q ∈ M →
        ∀ k, k ∉ M →
          (PathAdjacent4 p k ↔ PathAdjacent4 q k) := fun q => by
      let byK : DecidablePred fun k : Fin 4 => k ∉ M →
          (PathAdjacent4 p k ↔ PathAdjacent4 q k) := fun _ => inferInstance
      let allK : Decidable (∀ k : Fin 4, k ∉ M →
          (PathAdjacent4 p k ↔ PathAdjacent4 q k)) :=
        @Fintype.decidableForallFintype _ _ byK inferInstance
      letI := allK
      infer_instance
    let allQ : Decidable (∀ q : Fin 4, q ∈ M →
        ∀ k, k ∉ M →
          (PathAdjacent4 p k ↔ PathAdjacent4 q k)) :=
      @Fintype.decidableForallFintype _ _ byQ inferInstance
    letI := allQ
    infer_instance
  exact @Fintype.decidableForallFintype _ _ byP inferInstance

/-- Primeness, specialized to the concrete graph `0—1—2—3`: every
module containing two different vertices is the whole vertex set. -/
def Path4Prime : Prop :=
  ∀ M : Cube 4, PathModule4 M →
    (∃ p, p ∈ M ∧ ∃ q, q ∈ M ∧ p ≠ q) →
      M = Finset.univ

instance instDecidablePath4Prime : Decidable Path4Prime := by
  unfold Path4Prime
  let byM : DecidablePred fun M : Cube 4 => PathModule4 M →
      (∃ p, p ∈ M ∧ ∃ q, q ∈ M ∧ p ≠ q) →
        M = Finset.univ := fun _ => inferInstance
  exact @Fintype.decidableForallFintype _ _ byM inferInstance

/-- This is the six-pair/three-subset check displayed in the manuscript's
proof that `P₄` is prime. -/
theorem path4_prime : Path4Prime := by
  decide

def rankOneFibre (a : Fin 4 → Fin 4) (c : Fin 4) : Cube 4 :=
  Finset.univ.filter fun i => a i = c

lemma rankOneFibre_is_module (a : Fin 4 → Fin 4)
    (hmodule : FibreModuleCondition a) (c : Fin 4) :
    PathModule4 (rankOneFibre a c) := by
  intro p hp q hq k hk
  simp only [rankOneFibre, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
  simp only [rankOneFibre, Finset.mem_filter, Finset.mem_univ, true_and] at hk
  by_cases hpq : p = q
  · subst q
    rfl
  · apply hmodule hpq (hp.trans hq.symm) k
    intro hka
    exact hk (hka.trans hp)

lemma collision_of_not_injective (a : Fin 4 → Fin 4)
    (ha : ¬Injective a) :
    ∃ p q, p ≠ q ∧ a p = a q := by
  by_contra hnone
  apply ha
  intro p q hpq
  by_contra hpqNe
  apply hnone
  exact ⟨p, q, hpqNe, hpq⟩

/-- Since `P₄` is prime, any noninjective rank-one map satisfying the
fibre-module condition is constant. -/
theorem rankOne_collapse_of_module (a : Fin 4 → Fin 4)
    (ha : ¬Injective a) (hmodule : FibreModuleCondition a) :
    ∃ c, ∀ i, a i = c := by
  rcases collision_of_not_injective a ha with ⟨p, q, hpq, heq⟩
  let M := rankOneFibre a (a p)
  have hpM : p ∈ M := by simp [M, rankOneFibre]
  have hqM : q ∈ M := by simp [M, rankOneFibre, heq]
  have hwhole : M = Finset.univ := path4_prime M
    (rankOneFibre_is_module a hmodule (a p))
    ⟨p, hpM, q, hqM, hpq⟩
  refine ⟨a p, fun i => ?_⟩
  have hiM : i ∈ M := by rw [hwhole]; simp
  simpa [M, rankOneFibre] using hiM

/-! ## The colouring of the six rank-two vertices -/

lemma exists_second_colour (u : Cube 4 → Cube 4)
    (hu : Cotransverse u) (a : Fin 4)
    (hcollapse : ∀ i, rankOneIndex u hu i = a) (E : RankTwo4) :
    ∃ c, c ≠ a ∧ u E.1 = {a, c} := by
  have hEne : E.1.Nonempty := Finset.card_pos.mp (by omega)
  rcases hEne with ⟨p, hpE⟩
  have haImage : a ∈ u E.1 := by
    rw [← hcollapse p]
    exact rankOneIndex_mem_image u hu hpE
  have hcardImage : (u E.1).card = 2 := by
    rw [rank_preservation u hu, E.2]
  have hcardErase : ((u E.1).erase a).card = 1 := by
    rw [Finset.card_erase_of_mem haImage, hcardImage]
  have heraseNonempty : ((u E.1).erase a).Nonempty :=
    Finset.card_pos.mp (by omega)
  rcases heraseNonempty with ⟨c, hcErase⟩
  have hcImage : c ∈ u E.1 := (Finset.mem_erase.mp hcErase).2
  have hca : c ≠ a := (Finset.mem_erase.mp hcErase).1
  refine ⟨c, hca, ?_⟩
  have hsub : ({a, c} : Cube 4) ⊆ u E.1 := by
    simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using
      And.intro haImage hcImage
  apply Finset.Subset.antisymm
  · intro x hx
    by_contra hxPair
    have hstrict : ({a, c} : Cube 4) ⊂ u E.1 :=
      (Finset.ssubset_iff_subset_ne).2 ⟨hsub, by
        intro heq
        exact hxPair (heq ▸ hx)⟩
    have := Finset.card_lt_card hstrict
    rw [Finset.card_pair hca.symm, hcardImage] at this
    omega
  · exact hsub

/-- The unique coordinate different from `a` in a rank-two image. -/
noncomputable def edgeColour (u : Cube 4 → Cube 4)
    (hu : Cotransverse u) (a : Fin 4)
    (hcollapse : ∀ i, rankOneIndex u hu i = a) (E : RankTwo4) : Fin 4 :=
  Classical.choose (exists_second_colour u hu a hcollapse E)

lemma edgeColour_ne (u : Cube 4 → Cube 4)
    (hu : Cotransverse u) (a : Fin 4)
    (hcollapse : ∀ i, rankOneIndex u hu i = a) (E : RankTwo4) :
    edgeColour u hu a hcollapse E ≠ a :=
  (Classical.choose_spec (exists_second_colour u hu a hcollapse E)).1

lemma edgeColour_spec (u : Cube 4 → Cube 4)
    (hu : Cotransverse u) (a : Fin 4)
    (hcollapse : ∀ i, rankOneIndex u hu i = a) (E : RankTwo4) :
    u E.1 = {a, edgeColour u hu a hcollapse E} :=
  (Classical.choose_spec (exists_second_colour u hu a hcollapse E)).2

def pairRankTwo (p q : Fin 4) (hpq : p ≠ q) : RankTwo4 :=
  ⟨{p, q}, Finset.card_pair hpq⟩

@[simp] lemma pairRankTwo_val (p q : Fin 4) (hpq : p ≠ q) :
    (pairRankTwo p q hpq).1 = {p, q} := rfl

/-- Every colour class lies wholly among the edges of `P₄`, or wholly
among its nonedges. -/
def ColourRefinesPath (c : RankTwo4 → Fin 4) : Prop :=
  ∀ E E', c E = c E' → (PathEdge4 E.1 ↔ PathEdge4 E'.1)

lemma F_rankTwo_equality_detects_path (E E' : RankTwo4)
    (heq : F E.1 = F E'.1) : PathEdge4 E.1 ↔ PathEdge4 E'.1 := by
  by_cases hE : PathEdge4 E.1 <;> by_cases hE' : PathEdge4 E'.1
  · exact ⟨fun _ => hE', fun _ => hE⟩
  · have hne : ({(0 : Fin 4), (1 : Fin 4)} : Cube 4) ≠ {0, 2} := by
      decide
    exact False.elim (hne (by simpa [F, E.2, E'.2, hE, hE'] using heq))
  · have hne : ({(0 : Fin 4), (2 : Fin 4)} : Cube 4) ≠ {0, 1} := by
      decide
    exact False.elim (hne (by simpa [F, E.2, E'.2, hE, hE'] using heq))
  · exact ⟨fun h => (hE h).elim, fun h => (hE' h).elim⟩

lemma edgeColour_refines_path (u : Cube 4 → Cube 4)
    (hu : Cotransverse u) (hkernel : KernelRefines u F)
    (a : Fin 4) (hcollapse : ∀ i, rankOneIndex u hu i = a) :
    ColourRefinesPath (edgeColour u hu a hcollapse) := by
  intro E E' hcolour
  apply F_rankTwo_equality_detects_path E E'
  apply hkernel
  rw [edgeColour_spec u hu a hcollapse E,
    edgeColour_spec u hu a hcollapse E', hcolour]

/-- A colouring has no rainbow triangle. -/
def NoRainbow (c : RankTwo4 → Fin 4) : Prop :=
  ∀ ⦃i j k : Fin 4⦄ (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
    c (pairRankTwo i j hij) = c (pairRankTwo i k hik) ∨
    c (pairRankTwo i j hij) = c (pairRankTwo j k hjk) ∨
    c (pairRankTwo i k hik) = c (pairRankTwo j k hjk)

lemma edgeColour_noRainbow (u : Cube 4 → Cube 4)
    (hu : Cotransverse u) (a : Fin 4)
    (hcollapse : ∀ i, rankOneIndex u hu i = a) :
    NoRainbow (edgeColour u hu a hcollapse) := by
  intro i j k hij hik hjk
  let Eij := pairRankTwo i j hij
  let Eik := pairRankTwo i k hik
  let Ejk := pairRankTwo j k hjk
  let cij := edgeColour u hu a hcollapse Eij
  let cik := edgeColour u hu a hcollapse Eik
  let cjk := edgeColour u hu a hcollapse Ejk
  by_contra hrainbow
  simp only [not_or] at hrainbow
  rcases hrainbow with ⟨hcijcik, hcijcjk, hcikcjk⟩
  have hcaij : cij ≠ a := edgeColour_ne u hu a hcollapse Eij
  have hcaik : cik ≠ a := edgeColour_ne u hu a hcollapse Eik
  have hcajk : cjk ≠ a := edgeColour_ne u hu a hcollapse Ejk
  let T : Cube 4 := {i, j, k}
  have hcardT : T.card = 3 := by
    simp [T, hij, hik, hjk]
  have hpairSub (E : RankTwo4) (hET : E.1 ⊆ T) : u E.1 ⊆ u T :=
    cotransverse_monotone u hu hET
  have hcijMem : cij ∈ u T := by
    apply hpairSub Eij
      (by simp [Eij, pairRankTwo, T])
    rw [edgeColour_spec u hu a hcollapse Eij]
    simp [cij]
  have hcikMem : cik ∈ u T := by
    apply hpairSub Eik
      (by simp [Eik, pairRankTwo, T])
    rw [edgeColour_spec u hu a hcollapse Eik]
    simp [cik]
  have hcjkMem : cjk ∈ u T := by
    apply hpairSub Ejk
      (by simp [Ejk, pairRankTwo, T])
    rw [edgeColour_spec u hu a hcollapse Ejk]
    simp [cjk]
  have haMem : a ∈ u T := by
    rw [← hcollapse i]
    exact rankOneIndex_mem_image u hu (by simp [T])
  have hfourSub : ({a, cij, cik, cjk} : Cube 4) ⊆ u T := by
    simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using
      ⟨haMem, hcijMem, hcikMem, hcjkMem⟩
  have hcardFour : ({a, cij, cik, cjk} : Cube 4).card = 4 := by
    apply Finset.card_eq_four.mpr
    exact ⟨a, cij, cik, cjk, hcaij.symm, hcaik.symm, hcajk.symm,
      hcijcik, hcijcjk, hcikcjk, rfl⟩
  have hcardImage : (u T).card = 3 := by
    rw [rank_preservation u hu, hcardT]
  have := Finset.card_le_card hfourSub
  omega

/-- The order condition induced by the preceding coordinate permutation. -/
def ColourOrdered (c : RankTwo4 → Fin 4) (σ : Equiv.Perm (Fin 4)) : Prop :=
  ∀ ⦃i j k : Fin 4⦄ (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
    σ i < σ j → σ j < σ k →
      c (pairRankTwo i j hij) ≤ c (pairRankTwo i k hik) ∧
      c (pairRankTwo i k hik) ≤ c (pairRankTwo j k hjk)

lemma permMap_singleton_four (σ : Equiv.Perm (Fin 4)) (i : Fin 4) :
    permMap σ ({i} : Cube 4) = {σ i} := by
  simp [permMap]

lemma permMap_pair_four (σ : Equiv.Perm (Fin 4)) (i j : Fin 4) :
    permMap σ ({i, j} : Cube 4) = {σ i, σ j} := by
  simp [permMap]

lemma edgeColour_ordered (h : Cube 4 → Cube 4) (hh : Transverse4 h)
    (σ : Equiv.Perm (Fin 4))
    (u : Cube 4 → Cube 4) (hu : Cotransverse u)
    (huDef : u = h ∘ permMap σ) (a : Fin 4)
    (hcollapse : ∀ i, rankOneIndex u hu i = a) :
    ColourOrdered (edgeColour u hu a hcollapse) σ := by
  intro i j k hij hik hjk hijOrder hjkOrder
  have hsingleton (r : Fin 4) : h {σ r} = {a} := by
    calc
      h {σ r} = u {r} := by
        rw [huDef]
        simp [Function.comp_apply, permMap_singleton_four]
      _ = {rankOneIndex u hu r} := rankOneIndex_spec u hu r
      _ = {a} := by rw [hcollapse r]
  have hpairs (p q : Fin 4) (hpq : p ≠ q) :
      h {σ p, σ q} =
        {a, edgeColour u hu a hcollapse (pairRankTwo p q hpq)} := by
    calc
      h {σ p, σ q} = u {p, q} := by
        rw [huDef]
        simp [Function.comp_apply, permMap_pair_four]
      _ = {a, edgeColour u hu a hcollapse (pairRankTwo p q hpq)} := by
        simpa using edgeColour_spec u hu a hcollapse (pairRankTwo p q hpq)
  exact hh.colourMonotone hijOrder hjkOrder
    (hsingleton i) (hsingleton j) (hsingleton k)
    (hpairs i j hij) (hpairs i k hik) (hpairs j k hjk)

/-! ## The finite Gallai/threshold obstruction on `P₄` -/

/-- The six unordered pairs, in the order `01,02,03,12,13,23`. -/
def pairByCode : Fin 6 → RankTwo4 :=
  fun r =>
    if r = 0 then pairRankTwo 0 1 (by decide)
    else if r = 1 then pairRankTwo 0 2 (by decide)
    else if r = 2 then pairRankTwo 0 3 (by decide)
    else if r = 3 then pairRankTwo 1 2 (by decide)
    else if r = 4 then pairRankTwo 1 3 (by decide)
    else pairRankTwo 2 3 (by decide)

def sixColourOf (c : RankTwo4 → Fin 4) : Fin 6 → Fin 4 :=
  fun r => c (pairByCode r)

/-- Lookup of a colour by an unordered pair.  The diagonal value is
irrelevant in every use. -/
def sixAt (c : Fin 6 → Fin 4) (i j : Fin 4) : Fin 4 :=
  if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then c 0
  else if (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) then c 1
  else if (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) then c 2
  else if (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) then c 3
  else if (i = 1 ∧ j = 3) ∨ (i = 3 ∧ j = 1) then c 4
  else c 5

lemma sixAt_sixColourOf (c : RankTwo4 → Fin 4)
    (i j : Fin 4) (hij : i ≠ j) :
    sixAt (sixColourOf c) i j = c (pairRankTwo i j hij) := by
  fin_cases i <;> fin_cases j
  all_goals try omega
  all_goals simp [sixAt, sixColourOf, pairByCode, pairRankTwo]
  all_goals
    apply congrArg c
    apply Subtype.ext
    ext x
    aesop

def EdgeCode (r : Fin 6) : Prop := r = 0 ∨ r = 3 ∨ r = 5

instance instDecidableEdgeCode (r : Fin 6) : Decidable (EdgeCode r) := by
  unfold EdgeCode
  infer_instance

lemma pairByCode_is_path (r : Fin 6) :
    PathEdge4 (pairByCode r).1 ↔ EdgeCode r := by
  fin_cases r <;> decide

def SixAvoids (a : Fin 4) (c : Fin 6 → Fin 4) : Prop :=
  ∀ r, c r ≠ a

instance instDecidableSixAvoids (a : Fin 4) (c : Fin 6 → Fin 4) :
    Decidable (SixAvoids a c) := by
  unfold SixAvoids
  exact @Fintype.decidableForallFintype _ _ (fun _ => inferInstance)
    inferInstance

def SixRefinesPath (c : Fin 6 → Fin 4) : Prop :=
  ∀ r s, c r = c s → (EdgeCode r ↔ EdgeCode s)

instance instDecidableSixRefinesPath (c : Fin 6 → Fin 4) :
    Decidable (SixRefinesPath c) := by
  unfold SixRefinesPath
  let byR : DecidablePred fun r : Fin 6 => ∀ s : Fin 6,
      c r = c s → (EdgeCode r ↔ EdgeCode s) := fun r => by
    let byS : DecidablePred fun s : Fin 6 =>
        c r = c s → (EdgeCode r ↔ EdgeCode s) := fun _ => inferInstance
    exact @Fintype.decidableForallFintype _ _ byS inferInstance
  exact @Fintype.decidableForallFintype _ _ byR inferInstance

lemma ColourRefinesPath.six {c : RankTwo4 → Fin 4}
    (hc : ColourRefinesPath c) : SixRefinesPath (sixColourOf c) := by
  intro r s hrs
  rw [← pairByCode_is_path r, ← pairByCode_is_path s]
  exact hc (pairByCode r) (pairByCode s) hrs

def SixNoRainbow (c : Fin 6 → Fin 4) : Prop :=
  ∀ i j k : Fin 4, i ≠ j → i ≠ k → j ≠ k →
    sixAt c i j = sixAt c i k ∨
    sixAt c i j = sixAt c j k ∨
    sixAt c i k = sixAt c j k

instance instDecidableSixNoRainbow (c : Fin 6 → Fin 4) :
    Decidable (SixNoRainbow c) := by
  unfold SixNoRainbow
  let byI : DecidablePred fun i : Fin 4 => ∀ j k : Fin 4,
      i ≠ j → i ≠ k → j ≠ k →
        sixAt c i j = sixAt c i k ∨
        sixAt c i j = sixAt c j k ∨
        sixAt c i k = sixAt c j k := fun i => by
    let byJ : DecidablePred fun j : Fin 4 => ∀ k : Fin 4,
        i ≠ j → i ≠ k → j ≠ k →
          sixAt c i j = sixAt c i k ∨
          sixAt c i j = sixAt c j k ∨
          sixAt c i k = sixAt c j k := fun j => by
      let byK : DecidablePred fun k : Fin 4 =>
          i ≠ j → i ≠ k → j ≠ k →
            sixAt c i j = sixAt c i k ∨
            sixAt c i j = sixAt c j k ∨
            sixAt c i k = sixAt c j k := fun _ => inferInstance
      exact @Fintype.decidableForallFintype _ _ byK inferInstance
    exact @Fintype.decidableForallFintype _ _ byJ inferInstance
  exact @Fintype.decidableForallFintype _ _ byI inferInstance

lemma NoRainbow.six {c : RankTwo4 → Fin 4} (hc : NoRainbow c) :
    SixNoRainbow (sixColourOf c) := by
  intro i j k hij hik hjk
  simpa [sixAt_sixColourOf c i j hij, sixAt_sixColourOf c i k hik,
    sixAt_sixColourOf c j k hjk] using hc hij hik hjk

def SixOrdered (c : Fin 6 → Fin 4) (ord : Fin 4 → Fin 4) : Prop :=
  ∀ i j k : Fin 4, ord i < ord j → ord j < ord k →
    sixAt c i j ≤ sixAt c i k ∧ sixAt c i k ≤ sixAt c j k

instance instDecidableSixOrdered (c : Fin 6 → Fin 4)
    (ord : Fin 4 → Fin 4) : Decidable (SixOrdered c ord) := by
  unfold SixOrdered
  let byI : DecidablePred fun i : Fin 4 => ∀ j k : Fin 4,
      ord i < ord j → ord j < ord k →
        sixAt c i j ≤ sixAt c i k ∧ sixAt c i k ≤ sixAt c j k :=
    fun i => by
      let byJ : DecidablePred fun j : Fin 4 => ∀ k : Fin 4,
          ord i < ord j → ord j < ord k →
            sixAt c i j ≤ sixAt c i k ∧ sixAt c i k ≤ sixAt c j k :=
        fun j => by
          let byK : DecidablePred fun k : Fin 4 =>
              ord i < ord j → ord j < ord k →
                sixAt c i j ≤ sixAt c i k ∧
                  sixAt c i k ≤ sixAt c j k := fun _ => inferInstance
          exact @Fintype.decidableForallFintype _ _ byK inferInstance
      exact @Fintype.decidableForallFintype _ _ byJ inferInstance
  exact @Fintype.decidableForallFintype _ _ byI inferInstance

lemma ColourOrdered.six {c : RankTwo4 → Fin 4}
    {σ : Equiv.Perm (Fin 4)} (hc : ColourOrdered c σ) :
    SixOrdered (sixColourOf c) σ := by
  intro i j k hijOrder hjkOrder
  have hij : i ≠ j := by
    intro h; subst j; exact (lt_irrefl (σ i)) hijOrder
  have hik : i ≠ k := by
    intro h; subst k; exact (lt_irrefl (σ i)) (lt_trans hijOrder hjkOrder)
  have hjk : j ≠ k := by
    intro h; subst k; exact (lt_irrefl (σ j)) hjkOrder
  simpa [sixAt_sixColourOf c i j hij, sixAt_sixColourOf c i k hik,
    sixAt_sixColourOf c j k hjk] using
      hc hij hik hjk hijOrder hjkOrder

def InjectiveOrder (ord : Fin 4 → Fin 4) : Prop := Injective ord

instance instDecidableInjectiveOrder (ord : Fin 4 → Fin 4) :
    Decidable (InjectiveOrder ord) := by
  unfold InjectiveOrder Function.Injective
  let byI : DecidablePred fun i : Fin 4 => ∀ j : Fin 4,
      ord i = ord j → i = j := fun i => by
    let byJ : DecidablePred fun j : Fin 4 => ord i = ord j → i = j :=
      fun _ => inferInstance
    exact @Fintype.decidableForallFintype _ _ byJ inferInstance
  exact @Fintype.decidableForallFintype _ _ byI inferInstance

/-- A six-coordinate formulation of the concrete colouring obstruction.
Putting injectivity before the colour quantifier mirrors the mathematical
choice of a linear vertex order. -/
def SixColourObstruction4 : Prop :=
  ∀ (a : Fin 4) (ord : Fin 4 → Fin 4), InjectiveOrder ord →
    ∀ c : Fin 6 → Fin 4,
      SixAvoids a c → SixRefinesPath c → SixNoRainbow c →
        SixOrdered c ord → False

def usedColours (c : Fin 6 → Fin 4) : Finset (Fin 4) :=
  Finset.univ.image c

def ThreeColourObstruction4 : Prop :=
  ∀ c : Fin 6 → Fin 4, (usedColours c).card = 3 →
    SixRefinesPath c → SixNoRainbow c → False

def TwoColourObstruction4 : Prop :=
  ∀ ord : Fin 4 → Fin 4, InjectiveOrder ord →
    ∀ c : Fin 6 → Fin 4, (usedColours c).card = 2 →
      SixRefinesPath c → SixOrdered c ord → False

def sixFunction (x0 x1 x2 x3 x4 x5 : Fin 4) : Fin 6 → Fin 4 :=
  fun r => if r = 0 then x0 else if r = 1 then x1 else if r = 2 then x2
    else if r = 3 then x3 else if r = 4 then x4 else x5

lemma sixFunction_eta (c : Fin 6 → Fin 4) :
    sixFunction (c 0) (c 1) (c 2) (c 3) (c 4) (c 5) = c := by
  funext r
  fin_cases r <;> simp [sixFunction]

def TupleRefinesPath (x0 x1 x2 x3 x4 x5 : Fin 4) : Prop :=
  x0 ≠ x1 ∧ x0 ≠ x2 ∧ x0 ≠ x4 ∧
  x3 ≠ x1 ∧ x3 ≠ x2 ∧ x3 ≠ x4 ∧
  x5 ≠ x1 ∧ x5 ≠ x2 ∧ x5 ≠ x4

instance instDecidableTupleRefinesPath (x0 x1 x2 x3 x4 x5 : Fin 4) :
    Decidable (TupleRefinesPath x0 x1 x2 x3 x4 x5) := by
  unfold TupleRefinesPath
  infer_instance

def TupleNoRainbow (x0 x1 x2 x3 x4 x5 : Fin 4) : Prop :=
  (x0 = x1 ∨ x0 = x3 ∨ x1 = x3) ∧
  (x0 = x2 ∨ x0 = x4 ∨ x2 = x4) ∧
  (x1 = x2 ∨ x1 = x5 ∨ x2 = x5) ∧
  (x3 = x4 ∨ x3 = x5 ∨ x4 = x5)

instance instDecidableTupleNoRainbow (x0 x1 x2 x3 x4 x5 : Fin 4) :
    Decidable (TupleNoRainbow x0 x1 x2 x3 x4 x5) := by
  unfold TupleNoRainbow
  infer_instance

def TupleThreeColourObstruction4 : Prop :=
  ∀ x0 x1 x2 x3 x4 x5 : Fin 4,
    (usedColours (sixFunction x0 x1 x2 x3 x4 x5)).card = 3 →
      TupleRefinesPath x0 x1 x2 x3 x4 x5 →
        TupleNoRainbow x0 x1 x2 x3 x4 x5 → False

instance instDecidableTupleThreeColourObstruction4 :
    Decidable TupleThreeColourObstruction4 := by
  unfold TupleThreeColourObstruction4
  let by0 : DecidablePred fun x0 : Fin 4 => ∀ x1 x2 x3 x4 x5 : Fin 4,
      (usedColours (sixFunction x0 x1 x2 x3 x4 x5)).card = 3 →
        TupleRefinesPath x0 x1 x2 x3 x4 x5 →
          TupleNoRainbow x0 x1 x2 x3 x4 x5 → False := fun x0 => by
    let by1 : DecidablePred fun x1 : Fin 4 => ∀ x2 x3 x4 x5 : Fin 4,
        (usedColours (sixFunction x0 x1 x2 x3 x4 x5)).card = 3 →
          TupleRefinesPath x0 x1 x2 x3 x4 x5 →
            TupleNoRainbow x0 x1 x2 x3 x4 x5 → False := fun x1 => by
      let by2 : DecidablePred fun x2 : Fin 4 => ∀ x3 x4 x5 : Fin 4,
          (usedColours (sixFunction x0 x1 x2 x3 x4 x5)).card = 3 →
            TupleRefinesPath x0 x1 x2 x3 x4 x5 →
              TupleNoRainbow x0 x1 x2 x3 x4 x5 → False := fun x2 => by
        let by3 : DecidablePred fun x3 : Fin 4 => ∀ x4 x5 : Fin 4,
            (usedColours (sixFunction x0 x1 x2 x3 x4 x5)).card = 3 →
              TupleRefinesPath x0 x1 x2 x3 x4 x5 →
                TupleNoRainbow x0 x1 x2 x3 x4 x5 → False := fun x3 => by
          let by4 : DecidablePred fun x4 : Fin 4 => ∀ x5 : Fin 4,
              (usedColours (sixFunction x0 x1 x2 x3 x4 x5)).card = 3 →
                TupleRefinesPath x0 x1 x2 x3 x4 x5 →
                  TupleNoRainbow x0 x1 x2 x3 x4 x5 → False := fun x4 => by
            let by5 : DecidablePred fun x5 : Fin 4 =>
                (usedColours (sixFunction x0 x1 x2 x3 x4 x5)).card = 3 →
                  TupleRefinesPath x0 x1 x2 x3 x4 x5 →
                    TupleNoRainbow x0 x1 x2 x3 x4 x5 → False :=
              fun _ => inferInstance
            exact @Fintype.decidableForallFintype _ _ by5 inferInstance
          exact @Fintype.decidableForallFintype _ _ by4 inferInstance
        exact @Fintype.decidableForallFintype _ _ by3 inferInstance
      exact @Fintype.decidableForallFintype _ _ by2 inferInstance
    exact @Fintype.decidableForallFintype _ _ by1 inferInstance
  exact @Fintype.decidableForallFintype _ _ by0 inferInstance

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- The `K₄` instance of the three-colour part of Gallai decomposition,
combined with primeness of `P₄`. -/
theorem tuple_three_colour_obstruction_four :
    TupleThreeColourObstruction4 := by
  decide

def pathTwoColour (edgeColour nonedgeColour : Fin 4) : Fin 6 → Fin 4 :=
  fun r => if EdgeCode r then edgeColour else nonedgeColour

def TupleTwoColourObstruction4 : Prop :=
  ∀ ord : Fin 4 → Fin 4, InjectiveOrder ord →
    ∀ edgeColour nonedgeColour : Fin 4, edgeColour ≠ nonedgeColour →
      SixOrdered (pathTwoColour edgeColour nonedgeColour) ord → False

instance instDecidableTupleTwoColourObstruction4 :
    Decidable TupleTwoColourObstruction4 := by
  unfold TupleTwoColourObstruction4
  let byOrd : DecidablePred fun ord : Fin 4 → Fin 4 =>
      InjectiveOrder ord → ∀ edgeColour nonedgeColour : Fin 4,
        edgeColour ≠ nonedgeColour →
          SixOrdered (pathTwoColour edgeColour nonedgeColour) ord → False :=
    fun ord => by
      let byE : DecidablePred fun edgeColour : Fin 4 => ∀ nonedgeColour : Fin 4,
          edgeColour ≠ nonedgeColour →
            SixOrdered (pathTwoColour edgeColour nonedgeColour) ord → False :=
        fun edgeColour => by
          let byN : DecidablePred fun nonedgeColour : Fin 4 =>
              edgeColour ≠ nonedgeColour →
                SixOrdered (pathTwoColour edgeColour nonedgeColour) ord → False :=
            fun _ => inferInstance
          exact @Fintype.decidableForallFintype _ _ byN inferInstance
      let allE : Decidable (∀ edgeColour nonedgeColour : Fin 4,
          edgeColour ≠ nonedgeColour →
            SixOrdered (pathTwoColour edgeColour nonedgeColour) ord → False) :=
        @Fintype.decidableForallFintype _ _ byE inferInstance
      letI := allE
      infer_instance
  exact @Fintype.decidableForallFintype _ _ byOrd inferInstance

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- The four-vertex instance of the vicinal-preorder/threshold obstruction
for `P₄` and its complement. -/
theorem tuple_two_colour_obstruction_four :
    TupleTwoColourObstruction4 := by
  decide

lemma cross_colour_ne {c : Fin 6 → Fin 4} (hc : SixRefinesPath c)
    {r s : Fin 6} (hr : EdgeCode r) (hs : ¬EdgeCode s) : c r ≠ c s := by
  intro hrs
  exact hs ((hc r s hrs).mp hr)

lemma SixRefinesPath.tuple {c : Fin 6 → Fin 4}
    (hc : SixRefinesPath c) :
    TupleRefinesPath (c 0) (c 1) (c 2) (c 3) (c 4) (c 5) := by
  refine ⟨cross_colour_ne hc (by decide) (by decide),
    cross_colour_ne hc (by decide) (by decide),
    cross_colour_ne hc (by decide) (by decide),
    cross_colour_ne hc (by decide) (by decide),
    cross_colour_ne hc (by decide) (by decide),
    cross_colour_ne hc (by decide) (by decide),
    cross_colour_ne hc (by decide) (by decide),
    cross_colour_ne hc (by decide) (by decide),
    cross_colour_ne hc (by decide) (by decide)⟩

lemma SixNoRainbow.tuple {c : Fin 6 → Fin 4}
    (hc : SixNoRainbow c) :
    TupleNoRainbow (c 0) (c 1) (c 2) (c 3) (c 4) (c 5) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [sixAt] using hc 0 1 2 (by decide) (by decide) (by decide)
  · simpa [sixAt] using hc 0 1 3 (by decide) (by decide) (by decide)
  · simpa [sixAt] using hc 0 2 3 (by decide) (by decide) (by decide)
  · simpa [sixAt] using hc 1 2 3 (by decide) (by decide) (by decide)

theorem three_colour_obstruction_four : ThreeColourObstruction4 := by
  intro c hcard hrefines hGallai
  apply tuple_three_colour_obstruction_four
    (c 0) (c 1) (c 2) (c 3) (c 4) (c 5)
  · rw [sixFunction_eta]
    exact hcard
  · exact hrefines.tuple
  · exact hGallai.tuple

lemma usedColours_mem (c : Fin 6 → Fin 4) (r : Fin 6) :
    c r ∈ usedColours c := by
  simp [usedColours]

lemma usedColours_card_le_three (a : Fin 4) (c : Fin 6 → Fin 4)
    (ha : SixAvoids a c) : (usedColours c).card ≤ 3 := by
  have hsub : usedColours c ⊆ (Finset.univ.erase a : Finset (Fin 4)) := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨r, -, rfl⟩
    simp [ha r]
  have hcardErase : (Finset.univ.erase a : Finset (Fin 4)).card = 3 := by
    rw [Finset.card_erase_of_mem (by simp)]
    simp
  rw [← hcardErase]
  exact Finset.card_le_card hsub

lemma usedColours_card_ge_two (c : Fin 6 → Fin 4)
    (hc : SixRefinesPath c) : 2 ≤ (usedColours c).card := by
  have hne : c 0 ≠ c 1 := cross_colour_ne hc (by decide) (by decide)
  have hsub : ({c 0, c 1} : Finset (Fin 4)) ⊆ usedColours c := by
    simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using
      And.intro (usedColours_mem c 0) (usedColours_mem c 1)
  have hcardPair : ({c 0, c 1} : Finset (Fin 4)).card = 2 :=
    Finset.card_pair hne
  rw [← hcardPair]
  exact Finset.card_le_card hsub

lemma usedColours_eq_pair (c : Fin 6 → Fin 4)
    (hcard : (usedColours c).card = 2) (hne : c 0 ≠ c 1) :
    usedColours c = {c 0, c 1} := by
  have hsub : ({c 0, c 1} : Finset (Fin 4)) ⊆ usedColours c := by
    simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using
      And.intro (usedColours_mem c 0) (usedColours_mem c 1)
  apply Finset.Subset.antisymm
  · intro x hx
    by_contra hxPair
    have hstrict : ({c 0, c 1} : Finset (Fin 4)) ⊂ usedColours c :=
      (Finset.ssubset_iff_subset_ne).2 ⟨hsub, by
        intro heq
        exact hxPair (heq ▸ hx)⟩
    have hlt := Finset.card_lt_card hstrict
    rw [Finset.card_pair hne, hcard] at hlt
    omega
  · exact hsub

lemma two_colour_is_path_colouring (c : Fin 6 → Fin 4)
    (hcard : (usedColours c).card = 2) (hrefines : SixRefinesPath c) :
    c = pathTwoColour (c 0) (c 1) := by
  have hne : c 0 ≠ c 1 :=
    cross_colour_ne hrefines (by decide) (by decide)
  have hrange := usedColours_eq_pair c hcard hne
  funext r
  have hmem : c r ∈ ({c 0, c 1} : Finset (Fin 4)) := by
    rw [← hrange]
    exact usedColours_mem c r
  have hcases : c r = c 0 ∨ c r = c 1 := by simpa using hmem
  by_cases hr : EdgeCode r
  · have hnotNonedge : c r ≠ c 1 :=
      cross_colour_ne hrefines hr (by decide : ¬EdgeCode (1 : Fin 6))
    have heq : c r = c 0 := hcases.resolve_right hnotNonedge
    simpa [pathTwoColour, hr] using heq
  · have hnotEdge : c r ≠ c 0 := by
      intro heq
      exact cross_colour_ne hrefines (by decide : EdgeCode (0 : Fin 6)) hr heq.symm
    have heq : c r = c 1 := hcases.resolve_left hnotEdge
    simpa [pathTwoColour, hr] using heq

theorem two_colour_obstruction_four : TwoColourObstruction4 := by
  intro ord hord c hcard hrefines hordered
  have hne : c 0 ≠ c 1 :=
    cross_colour_ne hrefines (by decide) (by decide)
  have hc : c = pathTwoColour (c 0) (c 1) :=
    two_colour_is_path_colouring c hcard hrefines
  rw [hc] at hordered
  exact tuple_two_colour_obstruction_four ord hord (c 0) (c 1) hne hordered

theorem six_colour_obstruction_four : SixColourObstruction4 := by
  intro a ord hord c havoids hrefines hGallai hordered
  have hle := usedColours_card_le_three a c havoids
  have hge := usedColours_card_ge_two c hrefines
  have hcases : (usedColours c).card = 2 ∨ (usedColours c).card = 3 := by
    omega
  rcases hcases with htwo | hthree
  · exact two_colour_obstruction_four ord hord c htwo hrefines hordered
  · exact three_colour_obstruction_four c hthree hrefines hGallai

/-! ## Assembly of the non-generation proof -/

lemma rankOne_comp_perm_not_injective (h : Cube 4 → Cube 4)
    (hh : Cotransverse h) (σ : Equiv.Perm (Fin 4))
    (hbad : ¬Injective (rankOneIndex h hh)) :
    ¬Injective
      (rankOneIndex (h ∘ permMap σ) (hh.comp (permMap_cotransverse σ))) := by
  intro hinjective
  apply hbad
  intro x y hxy
  have hformula (z : Fin 4) :
      rankOneIndex (h ∘ permMap σ) (hh.comp (permMap_cotransverse σ)) z =
        rankOneIndex h hh (σ z) := by
    calc
      rankOneIndex (h ∘ permMap σ) (hh.comp (permMap_cotransverse σ)) z =
          rankOneIndex h hh
            (rankOneIndex (permMap σ) (permMap_cotransverse σ) z) :=
        rankOneIndex_comp (permMap σ) h (permMap_cotransverse σ) hh z
      _ = rankOneIndex h hh (σ z) := by rw [rankOneIndex_perm]
  have hpreimage : (σ.symm x : Fin 4) = σ.symm y := by
    apply hinjective
    calc
      rankOneIndex (h ∘ permMap σ) (hh.comp (permMap_cotransverse σ))
          (σ.symm x) = rankOneIndex h hh x := by
            rw [hformula, σ.apply_symm_apply]
      _ = rankOneIndex h hh y := hxy
      _ = rankOneIndex (h ∘ permMap σ)
          (hh.comp (permMap_cotransverse σ)) (σ.symm y) := by
            rw [hformula, σ.apply_symm_apply]
  exact σ.symm.injective hpreimage

/-- The path-graph map is absent even from the enlarged symmetric closure
whose nonsymmetric generators merely satisfy the three consequences of
Proposition 2.13 recorded by `Transverse4`. -/
theorem F_not_symGenerated : ¬SymGenerated F := by
  intro hgenerated
  rcases generated_has_first_transverse_factor hgenerated with
    ⟨h, g, σ, hh, hbad, hfactor⟩
  let u : Cube 4 → Cube 4 := h ∘ permMap σ
  have hu : Cotransverse u := hh.cotransverse.comp (permMap_cotransverse σ)
  have hbadU : ¬Injective (rankOneIndex u hu) := by
    simpa [u] using rankOne_comp_perm_not_injective h hh.cotransverse σ hbad
  have hfactorU : F = g ∘ u := by
    funext A
    simpa [u, Function.comp_apply] using congrFun hfactor A
  have hkernel : KernelRefines u F := by
    rw [hfactorU]
    exact kernelRefines_of_factor u g
  have hmodule : FibreModuleCondition (rankOneIndex u hu) :=
    fibreModuleCondition_of_kernel u hu hkernel
  rcases rankOne_collapse_of_module (rankOneIndex u hu) hbadU hmodule with
    ⟨a, hcollapse⟩
  let κ : RankTwo4 → Fin 4 := edgeColour u hu a hcollapse
  let c : Fin 6 → Fin 4 := sixColourOf κ
  apply six_colour_obstruction_four a σ σ.injective c
  · intro r
    exact edgeColour_ne u hu a hcollapse (pairByCode r)
  · exact (edgeColour_refines_path u hu hkernel a hcollapse).six
  · exact (edgeColour_noRainbow u hu a hcollapse).six
  · exact (edgeColour_ordered h hh σ u hu rfl a hcollapse).six

theorem cotransverse_not_generated_by_transverse_and_symmetries :
    ∃ f : Cube 4 → Cube 4, Cotransverse f ∧ ¬SymGenerated f :=
  ⟨F, F_cotransverse, F_not_symGenerated⟩

/-! The following wrapper makes the bridge to the paper's actual
`widehat-square` explicit. -/

inductive ActualSymStep4 (T : (Cube 4 → Cube 4) → Prop) where
  | perm (σ : Equiv.Perm (Fin 4))
  | transverse (h : Cube 4 → Cube 4) (hh : T h)

def ActualSymStep4.eval {T : (Cube 4 → Cube 4) → Prop} :
    ActualSymStep4 T → Cube 4 → Cube 4
  | .perm σ => permMap σ
  | .transverse h _ => h

def evalActualSymWord {T : (Cube 4 → Cube 4) → Prop} :
    List (ActualSymStep4 T) → Cube 4 → Cube 4
  | [], A => A
  | s :: w, A => evalActualSymWord w (s.eval A)

def GeneratedByActualAndSymmetries
    (T : (Cube 4 → Cube 4) → Prop) (f : Cube 4 → Cube 4) : Prop :=
  ∃ w : List (ActualSymStep4 T), evalActualSymWord w = f

def ActualSymStep4.toSymStep {T : (Cube 4 → Cube 4) → Prop}
    (hincluded : ∀ h, T h → Transverse4 h) : ActualSymStep4 T → SymStep4
  | .perm σ => .perm σ
  | .transverse h hh => .transverse h (hincluded h hh)

lemma eval_map_toSymStep {T : (Cube 4 → Cube 4) → Prop}
    (hincluded : ∀ h, T h → Transverse4 h) (w : List (ActualSymStep4 T)) :
    evalSymWord (w.map (ActualSymStep4.toSymStep hincluded)) =
      evalActualSymWord w := by
  funext A
  induction w generalizing A with
  | nil => rfl
  | cons s w ih =>
      cases s <;> exact ih _

/-- Any class of endomorphisms contained in `Transverse4` has a symmetric
closure not containing `F`.  Proposition 2.13 supplies `hincluded` for the
endomorphisms of the paper's `widehat-square`. -/
theorem F_not_generated_by_actual_and_symmetries
    (T : (Cube 4 → Cube 4) → Prop)
    (hincluded : ∀ h, T h → Transverse4 h) :
    ¬GeneratedByActualAndSymmetries T F := by
  intro hgenerated
  apply F_not_symGenerated
  rcases hgenerated with ⟨w, hw⟩
  refine ⟨w.map (ActualSymStep4.toSymStep hincluded), ?_⟩
  rw [eval_map_toSymStep]
  exact hw

end CotransverseNotGeneratedByTransverseAndSymmetries
