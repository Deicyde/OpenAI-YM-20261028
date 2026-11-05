import YM.Maxwell.Wick
import Mathlib.LinearAlgebra.Multilinear.Curry

/-! The definition using slot number counts each unordered pair once. -/
set_option autoImplicit false
noncomputable section
namespace YM.Maxwell.Wick
open Function Set Filter Equiv
open scoped Topology ContDiff BigOperators

namespace Occ
variable {n m : ℕ} {G : Gauge} {W : Powers G n} {Y : Powers G m}

variable (f : Fin n → Fin m) (hf : Injective f)

/-- Reindex occurrences, allowing deletion/insertion of zero powers. -/
theorem reindex (hf : Injective f) (h : ∀ i, Y (f i) = W i) (eh : ∀ k : Fin m, k ∉ Set.range f → Y k=0) :
    ∃ e : Occ W ≃ Occ Y, (∀ p, (e p).label = f p.label) ∧
      (∀ p, (e p).probe = p.probe) ∧ (∀ p, (e p).index = p.index) := by
  let L (p : Occ W) : Occ Y := atSlot (f p.label) p.probe p.index (by rw [h]; exact p.legit)
  have hu : Injective L := by
    intro p q he
    have hs := congr_arg (probe (W := Y)) he; have hk := congr_arg (index (W := Y)) he
    refine ext (hf ?_) hs hk; exact congr_arg (label (W := Y)) he
  have hs : Surjective L := by
    intro v
    by_cases ht : v.label ∈ Set.range f
    · rcases ht with ⟨l, hl⟩
      refine ⟨atSlot l v.probe v.index ?_,ext ?_ ?_ ?_⟩
      · rw [← h l, hl]; exact v.legit
      · exact hl
      · simp [L]
      simp [L]
    have hp := v.legit
    rw [eh _ ht] at hp
    exact Nat.not_lt_zero _ hp |>.elim
  exact ⟨Equiv.ofBijective L ⟨hu,hs⟩, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

lemma induced (hf : Injective f) {e : Occ W ≃ Occ Y} (h : ∀ p, (e p).label=f (label p)) :
    ∃ L : Matching W ≃ Matching Y, ∀ P v, e (partner P v) = partner (L P) (e v) := by
  -- subtypes on permutations
  let X := e.permCongr
  have he (s : Equiv.Perm (Occ W)) (v : Occ W) : X s (e v) = e (s v) := by simp [X]
  have hh (s : Equiv.Perm (Occ W)) : s * s = 1 ↔ (X s) * (X s) = 1 := by
    constructor
    · intro hx; ext1 w
      obtain ⟨w,rfl⟩ := e.surjective w
      simpa [Perm.mul_apply, he] using congr_arg e (show s (s w) = w from DFunLike.congr_fun hx w)
    intro hx; ext1 w
    apply e.injective
    change e (s (s w)) = e w
    rw [← he, ← he]; exact DFunLike.congr_fun hx (e w)
  let L : Matching W ≃ Matching Y := Equiv.subtypeEquiv X (by
    intro s
    rw [hh]
    apply and_congr_right
    intro _
    constructor
    · intro H x
      obtain ⟨x,rfl⟩ := e.surjective x
      rw [he, h,h]; exact hf.ne (H x)
    intro H x
    have hw := H (e x); rw [he,h,h] at hw
    exact fun Hs => hw (congr_arg f Hs))
  exact ⟨L,fun P v => (he _ _).symm⟩

def toCorner (P : Matching W) (p : Occ W) : Occ W := if p ∈ corners P then p else partner P p

theorem fixed (P : Matching W) {p : Occ W} (h : p ∈ corners P) : toCorner P p = p := by simp [toCorner,h]

theorem inside (P : Matching W) (p : Occ W) : toCorner P p ∈ corners P := by
  unfold toCorner; split_ifs with H
  · exact H
  exact (orientation _ _).mpr H

@[simp] theorem canonical (P : Matching W) (p : Occ W) : toCorner P (partner P p) = toCorner P p := by
  by_cases hp : p ∈ corners P <;> simp [toCorner,orientation,hp]

lemma cornerEquivProof (e : Occ W ≃ Occ Y) (P Q) (h : ∀ p, partner Q (e p) = e (partner P p)) (p) :
    toCorner P (e.symm (toCorner Q (e p))) = toCorner P p := by
  by_cases H : e p ∈ corners Q
  · rw [fixed Q H,e.symm_apply_apply]
  rw [show toCorner Q (e p) = partner Q (e p) from if_neg H, h, e.symm_apply_apply, canonical]

lemma graph_agree (e : Occ W ≃ Occ Y) (x : Points n) (y : Points m) (hx : x ∈ conf n)
    (hE : ∀ a b, edge y (e a) (e b) = edge x a b) (P Q) (h : ∀ p, partner Q (e p) = e (partner P p)) :
    graph x P = graph y Q := by
  have hw (p) : partner P (e.symm p) = e.symm (partner Q p) := by
    apply e.injective; rw [← h, e.apply_symm_apply, e.apply_symm_apply]
  apply Finset.prod_bij' (fun p _ => toCorner Q (e p)) (fun q _ => toCorner P (e.symm q))
    (fun p _ => inside ..) (fun q _ => inside ..)
    (fun p hp => (cornerEquivProof e P Q h p).trans (fixed P hp))
    (fun q hq => (cornerEquivProof e.symm Q P hw q).trans (fixed Q hq))
  intro p _
  by_cases hc : e p ∈ corners Q
  · rw [fixed Q hc, h,hE]
  simp only [toCorner, if_neg hc,turn,h,hE]
  exact entry_symmetric _ _ ((show Injective x.ofLp from hx).ne (different P p).symm)
end Occ
open Occ

variable {G : Gauge} {n m : ℕ}
theorem monExtension {Y : Powers G m} {W : Powers G n} (f : Fin n → Fin m) (H : Injective f) {x y}
    (hx : x ∈ conf n) (hy : ∀ i, y (f i) = x i)
    (hk : ∀ i, Y (f i) = W i) (hl : ∀ k, k ∉ Set.range f → Y k=0) :
    monomial x W = monomial (points y) Y := by
  obtain ⟨e, he, hs, -⟩ := reindex f H hk hl
  obtain ⟨L,hL⟩ := induced f H he
  refine Fintype.sum_equiv L _ _ fun p => graph_agree e _ _ hx ?_ p (L p) fun i => (hL p i).symm
  intro i k; simp [edge,he,hs,hy]

theorem exchangeSites (s : Equiv.Perm (Fin n)) {x} (hx : x ∈ conf n) (v : Fin n → WickPol G) :
    moment G x v = moment G (points (x.ofLp ∘ s)) (v ∘ s) := by
  let e : Fin n → Fin n := s
  let y := x.ofLp ∘ s
  have he : moment G x = (moment G (points y)).domDomCongr s := by
    refine Module.Basis.ext_multilinear (fun _ => monBasis G) ?_
    intro W
    rw [moment_basis]
    change monomial x W = moment G (points y) (fun i => monBasis G (W (s i)))
    rw [show (fun i => monBasis G (W (s i))) = fun i => monBasis G ((W ∘ s) i) from rfl]
    rw [moment_basis]
    exact monExtension s.symm s.symm.injective hx (by simp [y]) (by simp) (by simp [s.symm.range_eq_univ])
  exact DFunLike.congr_fun he v

theorem adjoin {x} (hx : x ∈ conf n) (y : E4) (v : Fin n → WickPol G) :
    moment G x v = moment G (Points.cons y x) (Fin.cons 1 v) := by
  let Y := Points.cons y x
  let M : MultilinearMap ℂ (fun _ : Fin n => WickPol G) ℂ := (moment G Y).curryLeft (1 : WickPol G)
  suffices h : moment G x = M from DFunLike.congr_fun h v
  refine Module.Basis.ext_multilinear (fun _ => monBasis G) ?_
  intro W
  rw [moment_basis]
  let W' : Powers G (n+1) := Fin.cons 0 W
  change monomial x W = moment G Y (Fin.cons 1 _)
  rw [show (Fin.cons (1 : WickPol G) (fun i => monBasis G (W i))) = fun i => monBasis G (W' i) by
    ext1 i; refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp [W',monBasis], moment_basis]
  refine monExtension Fin.succ (Fin.succ_injective n) hx ?_ ?_ ?_
  · simp
  · simp [W']
  intro i hi
  by_cases he : i=0
  · simp [he,W']
  exact (hi (show i ∈ Set.range Fin.succ from ⟨_, i.succ_pred he⟩)).elim

theorem constants (x : Points n) : moment G x (fun _ => 1) = 1 := by
  classical
  let A : Powers G n := fun _ => 0
  rw [show (fun _ : Fin n => (1 : WickPol G)) = (fun i => monBasis G (A i)) by simp [monBasis,A], moment_basis]
  haveI : IsEmpty (Occ A) := ⟨fun p => Nat.not_lt_zero _ p.legit⟩
  haveI : Subsingleton (Matching A) := by unfold Matching; infer_instance
  haveI : Unique (Matching A) := uniqueOfSubsingleton (⟨1,mul_one _, fun v => isEmptyElim v⟩ : Matching A)
  simp [monomial,Occ.graph, Subsingleton.elim (corners (W := A) _) ∅]
end YM.Maxwell.Wick
