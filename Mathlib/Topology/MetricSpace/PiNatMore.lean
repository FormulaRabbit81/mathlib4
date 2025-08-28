/-
Copyright (c) 2025 Janette Setälä, Yaël Dillies, Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Janette Setälä, Yaël Dillies, Kalle Kytölä
-/
import Mathlib.Analysis.NormedSpace.FunctionSeries
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.UnitInterval

/-!
# Embedding a countably separated space inside a space of sequences

This file proves that a topological `X` separated by countably many continuous functions `X → Y i`
where the `Y i` are metric spaces, then `X` can be embedded inside the product `∀ i, Y i`.
-/

open Encodable Function TopologicalSpace Topology
open scoped PiCountable unitInterval

variable {ι X : Type*} {Y : ι → Type*} {f : ∀ i, X → Y i}

namespace Metric

include f in
variable (X Y f) in
/-- Given a type `X` and a sequence `Y` of metric spaces and a sequence `f : : ∀ i, X → Y i` of
separating functions, `PiNatEmbed X Y f` is a type synonym for `X` seen as a subset of `∀ i, Y i`.
-/
structure PiNatEmbed (X : Type*) (Y : ι → Type*) (f : ∀ i, X → Y i) where
  /-- The map from `X` to the subset of `∀ i, Y i`. -/
  toPiNat ::
  /-- The map from the subset of `∀ i, Y i` to `X`. -/
  ofPiNat : X

namespace PiNatEmbed

@[ext] lemma ext {x y : PiNatEmbed X Y f} (hxy : x.ofPiNat = y.ofPiNat) : x = y := by
  cases x; congr!

variable (X Y f) in
/-- Equivalence between `X` and its embedding into `∀ i, Y i`. -/
@[simps]
def toPiNatEquiv : X ≃ PiNatEmbed X Y f where
  toFun := toPiNat
  invFun := ofPiNat
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] lemma ofPiNat_inj {x y : PiNatEmbed X Y f} :  x.ofPiNat = y.ofPiNat ↔ x = y :=
  (toPiNatEquiv X Y f).symm.injective.eq_iff

@[simp] lemma «forall» {P : PiNatEmbed X Y f → Prop} : (∀ x, P x) ↔ ∀ x, P (toPiNat x) :=
  (toPiNatEquiv X Y f).symm.forall_congr_left

variable (X Y f) in
/-- `X` equipped with the distance coming from `∀ i, Y i` embeds in `∀ i, Y i`. -/
noncomputable def embed : PiNatEmbed X Y f → ∀ i, Y i := fun x i ↦ f i x.ofPiNat

lemma embed_injective (separating_f : Pairwise fun x y ↦ ∃ i, f i x ≠ f i y) :
    Injective (embed X Y f) := by
  simpa [Pairwise, not_imp_comm (a := _ = _), funext_iff, Function.Injective] using separating_f

variable [Encodable ι]

section PseudoEMetricSpace
variable [∀ i, PseudoEMetricSpace (Y i)]

noncomputable instance : PseudoEMetricSpace (PiNatEmbed X Y f) :=
  .induced (embed X Y f) PiCountable.pseudoEMetricSpace

lemma edist_def (x y : PiNatEmbed X Y f) :
    edist x y = ∑' i, min (2⁻¹ ^ encode i) (edist (f i x.ofPiNat) (f i y.ofPiNat)) := rfl

lemma isometry_embed : Isometry (embed X Y f) := PseudoEMetricSpace.isometry_induced _

end PseudoEMetricSpace

section PseudoMetricSpace
variable [∀ i, PseudoMetricSpace (Y i)]

noncomputable instance : PseudoMetricSpace (PiNatEmbed X Y f) :=
  .induced (embed X Y f) PiCountable.pseudoMetricSpace

lemma dist_def (x y : PiNatEmbed X Y f) :
    dist x y = ∑' i, min (2⁻¹ ^ encode i) (dist (f i x.ofPiNat) (f i y.ofPiNat)) := rfl

variable [TopologicalSpace X]

lemma continuous_toPiNat (continuous_f : ∀ i, Continuous (f i)) :
    Continuous (toPiNat : X → PiNatEmbed X Y f) := by
  rw [continuous_iff_continuous_dist]
  simp only [dist_def]
  exact continuous_tsum (by fun_prop) summable_geometric_two_encode <| by simp [abs_of_nonneg]

end PseudoMetricSpace

section EMetricSpace
variable [∀ i, EMetricSpace (Y i)]

/-- If the functions `f i : X → Y i` separate points of `X`, then `X` can be embedded into
`∀ i, Y i`. -/
noncomputable abbrev emetricSpace (separating_f : Pairwise fun x y ↦ ∃ i, f i x ≠ f i y) :
    EMetricSpace (PiNatEmbed X Y f) :=
  .induced (embed X Y f) (embed_injective separating_f) PiCountable.emetricSpace

lemma isUniformEmbedding_embed (separating_f : Pairwise fun x y ↦ ∃ i, f i x ≠ f i y) :
    IsUniformEmbedding (embed X Y f) :=
  let := emetricSpace separating_f; isometry_embed.isUniformEmbedding

end EMetricSpace

open Set
section MetricSpace
variable [∀ i, MetricSpace (Y i)]

/-- If the functions `f i : X → Y i` separate points of `X`, then `X` can be embedded into
`∀ i, Y i`. -/
noncomputable abbrev metricSpace (separating_f : Pairwise fun x y ↦ ∃ i, f i x ≠ f i y) :
    MetricSpace (PiNatEmbed X Y f) :=
  (emetricSpace separating_f).toMetricSpace fun x y ↦ by simp [← ENNReal.ofReal_dist]

section CompactSpace
variable [TopologicalSpace X] [CompactSpace X]

lemma isHomeomorph_toPiNat (continuous_f : ∀ i, Continuous (f i))
    (separating_f : Pairwise fun x y ↦ ∃ i, f i x ≠ f i y) :
    IsHomeomorph (toPiNat : X → PiNatEmbed X Y f) := by
  letI := emetricSpace separating_f
  rw [isHomeomorph_iff_continuous_bijective]
  exact ⟨continuous_toPiNat continuous_f, (toPiNatEquiv X Y f).bijective⟩

variable (X Y f) in
/-- Homeomorphism between `X` and its embedding into `∀ i, Y i` induced by a separating family of
continuous functions `f i : X → Y i`. -/
@[simps!]
noncomputable def toPiNatHomeo (continuous_f : ∀ i, Continuous (f i))
    (separating_f : Pairwise fun x y ↦ ∃ i, f i x ≠ f i y) :
    X ≃ₜ PiNatEmbed X Y f :=
  (toPiNatEquiv X Y f).toHomeomorphOfIsInducing
    (isHomeomorph_toPiNat continuous_f separating_f).isInducing

end CompactSpace

open TopologicalSpace Filter

variable [MetricSpace X] [SeparableSpace X]

variable (X) in
/-Embedding function into 1 direction of countable cube-/
noncomputable abbrev T_func (n : ℕ) (x : X) : I :=
  have : Nonempty X := ⟨x⟩
  projIcc _ _ zero_le_one <| dist x (denseSeq X n)

lemma continuous_T (n : ℕ) : Continuous (T_func X n) := by
  cases isEmpty_or_nonempty X
  · exact continuous_of_discreteTopology
  refine continuous_projIcc.comp <| Continuous.dist continuous_id' ?_
  convert continuous_const (y := denseSeq X n)

lemma separation (x : X) (C : Set X) (hC : IsClosed C) (hnC : Nonempty C) (hx : x ∉ C) :
    ∃ (ε : ℝ) (n : ℕ), 0 < ε ∧ T_func X n x ≤ ε / 3 ∧ ∀ y ∈ C, (T_func X n y) ≥ 2 * ε / 3 := by
  let ε' : ℝ := min (infDist x C) 1
  have ε'_pos : ε' / 3 > 0 := by
    simpa [ε'] using (hC.notMem_iff_infDist_pos .of_subtype).mp hx
  have : Nonempty X := ⟨x⟩
  obtain ⟨n, hn⟩ : ∃ n, dist x (denseSeq X n) < ε' / 3 :=
    denseRange_iff.1 (denseRange_denseSeq X) x (ε' / 3) ε'_pos
  refine ⟨ε', n, ?_, ?_, ?_⟩
  · simpa [ε'] using (IsClosed.notMem_iff_infDist_pos hC Nonempty.of_subtype).mp hx
  · simpa [T_func, coe_projIcc] using .inr hn.le
  intro y hy
  simp [T_func, coe_projIcc]
  constructor
  · ring_nf; exact mul_le_one₀ (by simp [ε']) (by positivity) (by linarith)
  calc
    dist y (denseSeq X n) ≥ dist x y - dist x (denseSeq X n) := by
      simp; rw [add_comm]; exact dist_triangle_right x y (denseSeq X n)
    _ ≥ infDist x C - ε' / 3 := by gcongr; exact infDist_le_dist_of_mem hy
    _ ≥ 2 * ε' / 3 := by
      have lbound_ε' : (infDist x C) ≥ ε' := by simp [ε']
      rw [ge_iff_le, le_sub_iff_add_le']
      apply le_trans _ lbound_ε'
      ring_nf; rfl


lemma injective_T : Pairwise fun x y ↦ ∃ n, T_func X n x ≠ T_func X n y := by
  intro x y hxy
  obtain ⟨ε, n, hεpos, lbound, ubound⟩ := separation x {y} isClosed_singleton
    (instNonemptyOfInhabited) (by simpa)
  use n; specialize ubound y rfl
  refine Subtype.coe_ne_coe.mp <| ne_of_lt ?_
  apply lbound.trans_lt
  apply lt_of_le_of_lt' ubound
  linarith

variable (A : Type*) [TopologicalSpace A]

theorem homeothingamajig : ∃ funn : X → ℕ → I, IsEmbedding funn := by
  let firststep : X ≃ₜ PiNatEmbed X (fun i => I) (T_func X) := {
    toFun := toPiNatEquiv X (fun i => I) (T_func X)
    invFun := ofPiNat
    left_inv _ := rfl
    right_inv _ := rfl
    continuous_toFun := by
      rw [toPiNatEquiv]; exact continuous_toPiNat <| fun i ↦ continuous_T i
    continuous_invFun := by
      refine SeqContinuous.continuous ?_
      intro txn tx h_conv_txn
      by_contra! hdoesnt
      rw [tendsto_atTop'] at hdoesnt
      simp only [gt_iff_lt, comp_apply, not_forall, not_exists, not_lt] at hdoesnt
      obtain ⟨ε, εpos, hwhat⟩ := hdoesnt
      simp at hwhat
      change ∀ (N : ℕ), ∃ n > N, ε ≤ dist (txn n).ofPiNat tx.ofPiNat at hwhat
      obtain ⟨subseq,hmonosubseq,hsepsubseq⟩ := Nat.exists_strictMono_subsequence hwhat
      have sep : tx.ofPiNat ∉ (closure <| Set.range (fun n => (txn <| subseq n).ofPiNat)) := by
        refine (infDist_pos_iff_notMem_closure
        (range_nonempty fun n ↦ (txn (subseq n)).ofPiNat)).mpr ?_
        rw [infDist_eq_iInf]
        apply lt_of_lt_of_le εpos
        refine (le_ciInf_set_iff (range_nonempty fun n ↦ (txn (subseq n)).ofPiNat) ?_).mpr ?_
        · use 0; simp [lowerBounds]
        · simp; refine fun a ↦ by rw [dist_comm]; exact hsepsubseq a
      have nonemp : Nonempty <| (closure <| Set.range (fun n => (txn <| subseq n).ofPiNat)) := by
        rw [@nonempty_coe_sort,
            closure_nonempty_iff]; exact range_nonempty fun n ↦ (txn (subseq n)).ofPiNat
      obtain ⟨δ, i, δpos, hlineq, hgreq⟩ :=
          separation tx.ofPiNat (closure
          <| Set.range (fun n => (txn <| subseq n).ofPiNat)) isClosed_closure
          nonemp sep
      rw [tendsto_atTop] at h_conv_txn
      specialize h_conv_txn ((2 ^ i)⁻¹ * (δ / 3)) (by positivity)
      rw [← eventually_atTop,eventually_iff_seq_eventually] at h_conv_txn
      specialize h_conv_txn subseq <| StrictMono.tendsto_atTop hmonosubseq
      have kc (n : ℕ) : 2 * δ / 3 ≤ (T_func X i (txn (subseq n)).ofPiNat) :=
        hgreq (txn (subseq n)).ofPiNat <| subset_closure <| mem_range_self n
      have closurethang (n : ℕ):
          (txn (subseq n)).ofPiNat ∈ closure (range fun m ↦ (txn (subseq m)).ofPiNat) := by
        refine mem_closure_range_iff.mpr ?_
        intro ε hε; use n; simpa using hε
      by_cases δsize : 3 < δ
      · linarith [kc 0, unitInterval.le_one (T_func X i (txn (subseq 0)).ofPiNat)]
      have total_dist (n : ℕ) :  (2 ^ i)⁻¹ * (δ / 3) ≤ dist (txn (subseq n)) tx  := by
        simp [dist]
        have summ : Summable fun i ↦ min ((2 ^ i) : ℝ)⁻¹
            |↑(embed X (fun i ↦ ↑I) (T_func X) (txn (subseq n)) i) -
            ↑(embed X (fun i ↦ ↑I) (T_func X) tx i)| := by
          apply Summable.of_norm_bounded (g:= (fun (n_1 : ℕ) ↦ (2 ^ n_1)⁻¹))
          · simp_rw [←one_div,←one_div_pow]; exact summable_geometric_two
          · intro i
            simp_rw [Real.norm_eq_abs]
            rw [← Real.dist_eq, abs_of_nonneg (by positivity)]
            exact min_le_left _
                (dist ↑(embed X (fun i ↦ ↑I) (T_func X) (txn (subseq n)) i)
                ↑(embed X (fun i ↦ ↑I) (T_func X) tx i))
        calc
          (2 ^ i)⁻¹ * (δ / 3) ≤ min (2 ^ i)⁻¹
              |↑(embed X (fun i ↦ ↑I) (T_func X) (txn (subseq n)) i) -
              ↑(embed X (fun i ↦ ↑I) (T_func X) tx i)| := by
            simp only [le_inf_iff, inv_pos, Nat.ofNat_pos, pow_pos, mul_le_iff_le_one_right]
            constructor; · linarith [δsize]
            refine le_abs.mpr ?_
            left
            simp [embed]
            refine le_tsub_of_add_le_left ?_
            specialize hgreq (txn (subseq n)).ofPiNat (closurethang n)
            apply le_trans _ hgreq
            apply le_trans (add_le_add_right hlineq ((2 ^ i)⁻¹ * (δ / 3))) ?_
            refine add_le_of_le_tsub_left_of_le ?_ ?_
            · linarith
            · rw [mul_div_assoc 2 δ 3,two_mul, add_sub_cancel_right,← one_mul (δ / 3)]
              bound
          _ ≤ ∑' (i : ℕ), min (2 ^ i)⁻¹ |↑(embed X (fun i ↦ ↑I) (T_func X) (txn (subseq n)) i) -
                ↑(embed X (fun i ↦ ↑I) (T_func X) tx i)| := by
            apply Summable.le_tsum (f := fun (i : ℕ) ↦
                min ((2 ^ i) : ℝ)⁻¹ |↑(embed X (fun i ↦ ↑I) (T_func X) (txn (subseq n)) i) -
                ↑(embed X (fun i ↦ ↑I) (T_func X) tx i)|) (i := i) ?_ ?_
            · exact summ
            · intro j hj; positivity
      simp [total_dist, -eventually_atTop, ← not_le, NeBot.ne] at h_conv_txn
  }
  let secondstep : PiNatEmbed X (fun i => I) (T_func X) → ℕ → I := embed _ _ _
  let isEmbedding_secondstep : IsEmbedding secondstep :=
      (isUniformEmbedding_embed injective_T).isEmbedding
  use (fun x ↦ secondstep (firststep x))
  exact Topology.IsEmbedding.comp (g:= secondstep) (isEmbedding_secondstep)
      (Homeomorph.isEmbedding firststep)


#lintunusedHavesSuffices
#exit

instance : SequentialSpace <| PiNatEmbed X (fun i => I) (T_func X) := FrechetUrysohnSpace.to_sequentialSpace

variable [TopologicalSpace X] [CompactSpace X] [∀ i, MetricSpace (Y i)]

/-- If `X` is compact, and there exists a sequence of continuous functions `f i : X → Y i` to
metric spaces `Y i` that separate points on `X`, then `X` is metrizable. -/
lemma TopologicalSpace.MetrizableSpace.of_countable_separating (f : ∀ i, X → Y i)
    (continuous_f : ∀ i, Continuous (f i)) (separating_f : Pairwise fun x y ↦ ∃ i, f i x ≠ f i y) :
    MetrizableSpace X :=
  letI := Metric.PiNatEmbed.metricSpace separating_f
  (Metric.PiNatEmbed.toPiNatHomeo X Y f continuous_f separating_f).isEmbedding.metrizableSpace
