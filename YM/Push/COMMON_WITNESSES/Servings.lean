import YM.Next.BOUNDARY.Stage
import YM.Push.COMMON_WITNESSES.GridBills
import YM.Push.COMMON_WITNESSES.Origins

/-!
# From centred single-field receipts to the finite Grill receipts

Geometry/payment isolation. All roots below already include reflection
hand; `ordinary` gets us back to the required real pair. Test all choices
of frame for those fields (a finite set). No assuming a joint plot on the
limiting S. We must still *buy* the single-field hypothesis at the
production sites (open).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Common
open Function Filter Set Extraction Cells Table Lattice MeasureTheory Next.Extract Wilson OS
open scoped Topology BigOperators ContDiff
open Extraction.Spin

variable {G : Gauge} {C : Family G} {d : ℕ}
variable {h N p n : ℕ}

def flipBook (f : Bool) : Signed := if f then Signed.mirror timeAxis else 1

variable (x : Fin n → Cover) (u : Caps n) (hu : ∀ i, u i ≤ d)

def stems (f : Bool) := (flipBook f).act ∘ x

def recipe (f : Bool) (s : Combo C u) (i : Fin n) : Flavour C d :=
    ⟨⟨u i,Nat.lt_succ_of_le (hu i)⟩, s i, flipBook f,false⟩

lemma recipes (f : Bool) (s : Combo C u) : herb ∘ recipe u hu f s = C.book.move (flipBook f) ∘ baseWord C u s := by
  funext i; change token C.book _ ⟨_,false⟩ = _; unfold token; simp only [Bool.false_eq_true,↓reduceIte]; rfl

def jump (t i : ℕ) : Cover := fun _ => t*i

variable (hN : h ≤ N) (Z : Flavour C d → Config G (C.side N p) → ℂ)


def platter (f : Bool) (s : Combo C u) (t j : ℕ) := production hN Z (recipe u hu f s) (stems x f) (jump t j)

def tasting (s : Combo C u) (t j : ℕ) (q : Config G (C.side N p)) :=
    platter x u hu hN Z false s t j q - platter x u hu hN Z true s t j q

lemma tasting_eq (hw : C.Makes) (hc : ∀ i : Flavour C d, C.ref (herb i).1 ≤ N) (s : Combo C u) (t j : ℕ) (q : Config G (C.side N p)) :
    tasting x u hu hN (bornField N p) s t j q = Grid.flash (C:=C) h (baseWord C u s) x N p t j q := by
  unfold tasting platter; rw [in_fields hN hw hc,in_fields hN hw hc,recipes,recipes]
  have hh : C.book.move 1 ∘ baseWord C u s = baseWord C u s := funext fun i => Spin.move_one ..
  have he : stems x false = x := funext fun i => by simp [stems,flipBook]
  simp only [he,flipBook, ↓reduceIte, Bool.false_eq_true, hh]; rfl

variable {W R δ : ℝ} (hz : ∀ i, DirectedField hN i (Z i) R δ) (H : C.Makes)
variable (hw : ∀ i : Flavour C d, centeredBudget C (herb i) W h N p)

include hz
private lemma stature (s : Combo C u) (f : Bool) (t j : ℕ) (_hr : 0 ≤ R) :
    let F := platter x u hu hN Z f s t j
    Measurable F ∧ ∀ q, ‖F q‖ ≤ R^n ∧ star (F q) = F q := by
  intro F
  let W := canvas C hN p
  let c := places C hN p (stems x f) (jump t j)
  let r i := relocate hN (c i) (recipe u hu f s i)
  have he i : Interior (W.chamber (c i)) (W.copy (c i) (Z (r i))) :=
    W.copies (c i) (hz _).behind
  change Measurable (fun q => ∏ i, W.copy (c i) (Z (r i)) q) ∧ _
  refine ⟨Finset.measurable_prod _ (fun i _ => (he i).borel),?_⟩
  intro q
  change ‖∏ i,W.copy (c i) (Z (r i)) q‖ ≤ R^n ∧ _
  have hy i : W.copy (c i) (Z (r i)) q = Z (r i) (pull (W.omega (c i)) (W.translateBy (c i)) q) := by
    unfold Tiling.copy; split; exacts [(hz _).ordinary _,rfl]
  constructor
  · simp_rw [norm_prod,hy]; exact (Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => (hz _).size _)).trans_eq
      (by simp)
  change star (∏ i,W.copy (c i) (Z (r i)) q) = ∏ i,W.copy (c i) (Z (r i)) q
  simp_rw [star_prod,hy, show ∀ i q, star (Z i q)=Z i q from fun i q => (hz i).ordinary q]

include H hw hu in
/-- One finite cut to pay the bills.

Keep the same Z throughout (e.g. do
not re-choose for each pair needed in the Gram comparison).

`gap` token here δ
is an absolute comparison error permitting ANY ε invocation later. -/
lemma sample_finite (hb : 0 ≤ W) (hR : 0 ≤ R) (hδ : 0 ≤ δ) (hδ' : δ ≤ 1)
    (k : ℕ) (A : GrillCosts) (ha : 2*R^n ≤ A.cap k)
    (hm : 4*((↑(n+n : ℕ) : ℝ)*(δ*(W+1)^(n+n))) ≤ toll k) (t J : ℕ)
    (hij : ∀ i j, i<j → j<J → A.past k i j≤t → ∀ a b : Bool, Injective
      (Fin.append (places C hN p (stems x a) (jump t i)) (places C hN p (stems x b) (jump t j)))) :
    ∃ y : Plots C u N p, Instalment C h x u A k N p t J y := by
  let B := tasting x u hu hN Z
  have hs (s i) : Measurable (B s t i) ∧ ∀ q, ‖B s t i q‖ ≤ A.cap k ∧ star (B s t i q) = B s t i q := by
    obtain ⟨hf,hF⟩ := stature x u hu hN Z hz s false t i hR
    obtain ⟨hh,hH⟩ := stature x u hu hN Z hz s true t i hR
    refine ⟨hf.sub hh,fun q => ?_⟩
    dsimp only [B, tasting]; rw [star_sub,(hF q).2,(hH q).2]
    exact ⟨(norm_sub_le ..).trans ((add_le_add (hF q).1 (hH q).1).trans (by linarith)),rfl⟩
  let y (i : ℕ) (s : Combo C u) (q : Config G (C.side N p)) := (B s t i q).re
  have hy i s q : (y i s q : ℂ) = B s t i q := Complex.conj_eq_iff_re.1 ((hs s i).2 q).2
  refine ⟨y,⟨fun j _ s => ⟨Complex.continuous_re.measurable.comp (hs s j).1, fun q =>
    le_trans (Complex.abs_re_le_norm _) ((hs s j).2 q).1⟩,?_⟩⟩
  intro i j h1 h2 h3 s v
  let c : ℝ := (↑(n+n : ℕ) : ℝ)*(δ*(W+1)^(n+n))
  let μ := law G (C.side N p) (C.beta N p)
  let ZZ := bornField (C:=C) (d:=d) N p
  let x1 D (a b : Bool) := ∫ q, platter x u hu hN D a s t i q * platter x u hu hN D b v t j q ∂μ
  let core D := x1 D false false - x1 D false true - (x1 D true false - x1 D true true)
  have ht (a b : Bool) : ‖x1 Z a b - x1 ZZ a b‖ ≤ c :=
    pair_filled hN Z W hb R δ hδ hδ' hz H hw _ _ _ _ _ _ (hij i j h1 h2 h3 _ _)
  have he (D : Flavour C d → Config G (C.side N p) → ℂ) (H : ∀ a, Interior ((canvas C hN p).chamber 0) (D a)) :
      (∫ q, (tasting x u hu hN D s t i q * tasting x u hu hN D v t j q).re ∂μ) = (core D).re := by
    let X a := platter x u hu hN D a s t i
    let Y a := platter x u hu hN D a v t j
    let F a b q := ((X a q)*(Y b q)).re
    have Hu a b : Integrable (fun q => X a q * Y b q) μ := lawfulPair hN D H _ _ _ _ _ _
    have HH a b : Integrable (F a b) μ := (Hu ..).re
    have HY a : Integrable (fun q => F a false q - F a true q) μ := (HH a false).sub (HH a true)
    have hb a b : (x1 D a b).re = ∫ q, F a b q ∂μ := (integral_re (Hu a b)).symm
    change (∫ q, ((X false q - X true q)*(Y false q-Y true q)).re ∂μ) = _
    unfold core
    simp_rw [sub_mul,mul_sub,Complex.sub_re,hb]
    rw [integral_sub (HY _) (HY _),integral_sub (HH ..) (HH ..),integral_sub (HH ..) (HH ..)]
  have hc i : C.ref (herb (C:=C) (d:=d) i).1 ≤ N := (hw i).choose_spec.1
  have heC : cross C h x u N p t i j s v = (core ZZ).re := by
    unfold cross; simp_rw [← tasting_eq x u hu hN H hc]
    exact he ZZ (fun a => ((hw a).choose_spec.2 0).1)
  have heZ : (∫ q, y i s q * y j v q ∂μ) = (core Z).re := by
    rw [← he Z (fun a => (hz a).behind)]; apply integral_congr_ae
    refine Eventually.of_forall fun q => ?_
    change _ = (B s t i q * B v t j q).re
    rw [← hy,← hy,← Complex.ofReal_mul,Complex.ofReal_re]
  have hh : ‖core Z-core ZZ‖ ≤ 4*c := by
    let m a b := x1 Z a b - x1 ZZ a b
    rw [show core Z-core ZZ=m false false-m false true-(m true false-m true true) by unfold core m; ring]
    refine (norm_sub_le ..).trans ?_
    have hb a : ‖m a false - m a true‖ ≤ c+c := (norm_sub_le ..).trans (add_le_add (ht ..) (ht ..))
    linarith [hb true,hb false]
  rw [heC,heZ,← Complex.sub_re]; exact (Complex.abs_re_le_norm _).trans (hh.trans hm)
end YM.Push.Common
