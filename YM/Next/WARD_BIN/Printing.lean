import YM.Next.WARD_BIN.Baton
import YM.Next.WARD_BIN.Coin
import YM.Next.WARD_BIN.Deposit
/-!
# Printing a dimensionless test at the top

Unmarked law, literal hop deposits on whole-geometry indices. Start with body
costs; retain all flags via masked primary and full-footprint `gap`. This
choice's forced contributions agree with `offer` after grouping -- matters for
joint discrepancy closer later. Other choices comparing by `Pressed` may live
at different ACTUAL indices in this SAME alphabet, no losing provenance.

No assumption of Woke/any marker iteration here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WardBin
open Function Filter Set MeasureTheory Wilson Lattice RG Source Labels Work.G07 Gas
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side} {H : Hol G} {k l m P N d : ℕ} {S : Finset Cover} {b : BudgetPoint}
    {F : Labels.Frame G d} {X : SectionData F} {R : Rep G n} {o : Site n} {t : ℝ}

abbrev Form (G : Gauge) := CoverConfig G → ℂ

def coat (H : Labels.Frame G d) (t : ℝ) : Label G d →ₗ[ℂ] H.Coeff := H.scaled t ∘ₗ H.coords.toLinearMap
lemma coat_flip (q : Label G d) (h : t≠0) : primary F t (coat F t q)=q := by
  unfold primary coat; simp only [LinearMap.comp_apply]
  rw [show F.scaled t⁻¹ _=_ from (by simpa only [inv_inv] using! F.scaled_inv (inv_ne_zero h) (F.coords q)),LinearEquiv.symm_apply_apply]

lemma write_unitpart (X : SectionData F) (hs : X.Sound H) (t : ℝ) (x : F.Coeff) (U : CoverConfig G) :
    canonical X t x U=x 0 + canonical X t (F.core x) U := by
  have hx : x 0 • F.e0 + F.core x=x := by
    funext i
    by_cases h : i=0
    · subst i; simp [Frame.e0,Labels.Frame.core]
    simp [Labels.Frame.core,Frame.e0,h]
  unfold canonical
  nth_rw 1 [← hx]; simp only [map_add,map_smul,F.scaled_unit,X.eval_linear.map_add,X.eval_linear.map_smul,
    hs.unit,Pi.add_apply,Pi.smul_apply,Pi.one_apply,smul_eq_mul,mul_one]

lemma canonical_linear (X : SectionData F) (t : ℝ) : IsLinearMap ℂ (canonical X t) :=
  ⟨fun a b => by unfold canonical; rw [map_add,X.eval_linear.map_add],
    fun a b => by unfold canonical; rw [map_smul,X.eval_linear.map_smul]⟩

def germ_v (X : SectionData F) (t : ℝ) (o : Site n) (u : Form G) (x : F.Coeff) : Config G n → ℂ :=
  places o (u-canonical X t x)
-- Earnings split, static masks. Equality locus included in masks.
def wages (X : SectionData F) (Y : Support n) (t : ℝ) (o : Site n) (u : Form G) (x : F.Coeff)
    (U : Config G n) := x 0 + masked t (X.footprint o) (places o (canonical X t (F.core x))) U +
      masked t Y (germ_v X t o u x) U

def gap (X : SectionData F) (Y : Support n) (t : ℝ) (o : Site n) (u : Form G) (x : F.Coeff) := places o u - wages X Y t o u x

variable {Y : Support n}
lemma placing {u : Form G} (h : LocalOn S u) : LocalOn (footprint S o) (places o u) := by
  simpa only [footprint,places,Finset.coe_image] using! LocalOn.expandAt ↑S u h o

lemma soup (X : SectionData F) (hs : X.Sound H) {u : Form G} {q : Label G d} {c : ℝ} (h : Coin H F S k b o u q c)
    (hp : X.stencil ⊆ S) (x : F.Coeff) : Fault b (footprint S o) (gap X (footprint S o) b.threshold o u x) := by
  let t := b.threshold
  let Y := footprint S o
  have hx : X.footprint o ⊆ footprint S o := Finset.image_subset_image hp
  let v := germ_v X b.threshold o u x
  have he (w : F.Coeff) : LocalOn (X.footprint o) (places o (canonical X t w)) := X.placed_local o _
  have hg : LocalOn (footprint S o) v := by
    intro U V hC
    apply congr_arg₂ (·-·) ((placing h.localizes) U V hC) ((he _) _ _ (agrees_mono hC fun _ h => hx h))
  have hm (w : F.Coeff) : GaugeInvariant (places o (canonical X t w)) := X.placed_invariant hs o _
  have hy : GaugeInvariant (places o u) := by
    intro k U; rw [places,Function.comp_apply,expandAt_gauge]; exact h.invariant _ _
  have hv : GaugeInvariant v := fun k U => congr_arg₂ (·-·) (hy _ U) (hm _ _ U)
  have hr (y : Support n) (U : Config G n) (V : Site n→G.El) (f : Config G n→ℂ) (he : GaugeInvariant f) :
      masked t y f (gauge V U)=masked t y f U := by
    have hh : Healthy t y (gauge V U) ↔ Healthy t y U := by rw [Healthy,Healthy, gauge_flags]
    by_cases hi : Healthy t y U
    · rw [masked_eq _ _ _ _ (hh.mpr hi),masked_eq _ _ _ _ hi, he V]
    rw [masked_ne _ _ _ _ (mt hh.mp hi),masked_ne _ _ _ _ hi]
  have hu (w : F.Coeff) : Continuous (places o (canonical X t w)) := X.continuous_places _ _
  have hw : Continuous (places o u) := h.smooth.comp (show Continuous (expandAt o (K:=G.El)) by unfold expandAt; fun_prop)
  refine ⟨fun U ho HH => ?_,fun k U => ?_,?_,fun U V hi hi' => ?_⟩
  · have he : Healthy t (X.footprint o) U := Disjoint.mono_left hx HH
    apply ho; rw [gap,Pi.sub_apply,wages,masked_eq _ _ _ _ HH,masked_eq _ _ _ _ he]
    unfold germ_v places; simp only [Pi.sub_apply, Function.comp_apply,write_unitpart X hs b.threshold x]; abel
  · rw [gap,Pi.sub_apply, Pi.sub_apply]
    apply congr_arg₂ (·-·) (hy k U)
    exact congr_arg₂ (·+·) (congrArg (x 0 + ·) (hr _ _ _ _ (hm _))) (hr _ _ _ _ hv)
  · have hb : Measurable v := (hw.sub (hu x)).measurable
    exact hw.measurable.sub ((measurable_const.add (masked_measurable _ _ _ (hu (F.core x)).measurable)).add
      (masked_measurable _ _ _ hb))
  have hk (f : Config G n → ℂ) (y : Support n) (he : y⊆Y) (hf : LocalOn y f) : masked t y f U = masked t y f V := by
    have h (A B : Config G n) (ha : Agrees y A B) (hh : y∩flags t A=y∩flags t B) :
        masked t y f A=masked t y f B := by
      have hy : Healthy t y A ↔ Healthy t y B := by simp only [Healthy,Finset.disjoint_iff_inter_eq_empty, hh]
      by_cases hv : Healthy t y A
      · rw [masked_eq _ _ _ _ hv,masked_eq _ _ _ _ (hy.mp hv),hf A B ha]
      rw [masked_ne _ _ _ _ hv, masked_ne _ _ _ _ (mt hy.mpr hv)]
    exact Work.H03.reads_larger he h U V hi hi'
  exact congr_arg₂ (·-·) ((placing h.localizes) U V hi) (congr_arg₂ (·+·)
    (congrArg (x 0 + ·) (hk _ _ hx (he _))) (hk _ _ (Finset.Subset.refl _) hg))

lemma wages_sub (u u' : Form G) (x x' : F.Coeff) (U : Config G n) :
    wages X Y t o (u-u') (x-x') U = wages X Y t o u x U - wages X Y t o u' x' U := by
  have hm {P : Support n} {f g : Config G n →ℂ} : masked t P (f-g) U=masked t P f U-masked t P g U := by
    by_cases h : Healthy t P U
    · simp only [masked_eq _ _ _ _ h]; rfl
    simp [masked_ne _ _ _ _ h]
  have hp : germ_v X t o (u-u') (x-x')=germ_v X t o u x - germ_v X t o u' x' := by
    funext U; simp only [germ_v,places,Function.comp_apply,(canonical_linear X t).map_sub,Pi.sub_apply]; abel
  have he {u v : Form G} : places o (u-v)=places o u-places o v := rfl
  unfold wages; rw [map_sub,(canonical_linear X t).map_sub,he,hp,hm,hm,Pi.sub_apply]; abel
lemma gap_sub (u u' : Form G) (x x' : F.Coeff) : gap X Y t o (u-u') (x-x')=gap X Y t o u x - gap X Y t o u' x' := by
  funext U; simp only [gap,wages_sub,places,Function.comp_apply,Pi.sub_apply]; abel

structure Pressed (X : SectionData F) (P : Coefficient F n) (Y : Support n) (t : ℕ) (o : Site n) (R : Rep G n)
    (u : Form G) : Prop where
  ink : P.support t=Y
  charge : P.regular=Pi.single t (germ_v X R.p.threshold o u P.x)
  force i U : bucket R.activities (fun j => P.forced j U) i = hop R.activities R.p Y (gap X Y R.p.threshold o u P.x) i U

namespace Pressed
variable {P Q : Coefficient F n} {t : ℕ} {u v : Form G}

lemma sub (h : Pressed X P Y t o R u) (he : Pressed X Q Y t o R v) {κ μ a b : ℝ}
    (hp : P.remBound o R κ a) (hq : Q.remBound o R μ b) : Pressed X (stepLess P Q) Y t o R (u-v) := by
  have hx : (stepLess P Q).x=P.x-Q.x := rfl
  refine ⟨h.ink,?_,fun i U => ?_⟩
  · rw [hx]; change P.regular-Q.regular= _
    rw [h.charge,he.charge]; ext1 i; by_cases ht : i=t
    · subst i; simp only [Pi.sub_apply,Pi.single_eq_same]; funext U
      simp only [germ_v,places,(canonical_linear X _).map_sub,Function.comp_apply,Pi.sub_apply]; abel
    simp [ht]
  change bucket R.activities (fun i => P.forced i U-Q.forced i U) _=_
  rw [hx, holds_sub ((tangents hp).summable U) ((tangents hq).summable U),h.force,he.force,gap_sub]; unfold hop tag
  split_ifs; exact (sub_mul ..).symm; simp




end Pressed

-- canon price of c separate (paid once per finite family & k/P)
def stipend (H : Hol G) (X : SectionData F) (b : BudgetPoint) (S : Finset Cover) (o : Site n) (c : ℝ) := ∀ x,
    Coin H F S b.order b o (canonical X b.threshold x) (primary F b.threshold x) (c*‖x‖)
lemma tips (X : SectionData F) (hs : X.Sound H) (hp : Bid.pop X) (ht : X.stencil ⊆ S) :
    ∃ c : ℝ, 1 ≤ c ∧ ∀ b : BudgetPoint,b.order=k → b.power=P → ∀ n,FitsIn S n → ∀ o : Site n, stipend H X b S o c := by
  obtain ⟨c,hc,H⟩ := primary_price X hs hp ht k P
  exact ⟨c,hc,fun b hb hv n he o x => hb.symm ▸ H _ he b hv _ _⟩

lemma outfit {u : Form G} {x : Label G d} {m c : ℝ} (h : Coin H F S b.order b o u x c)
    (hm : 1 ≤ m) (g : stipend H X b S o m) : Coin H F S b.order b o
    (canonical X b.threshold (coat F b.threshold x)) x (m*c) := by
  have hz := g (coat F b.threshold x); rw [coat_flip x b.threshold_pos.ne'] at hz
  exact hz.raise (mul_le_mul_of_nonneg_left ((coeff_le (coat F b.threshold x)).trans h.weights) (by linarith))

lemma gap_value {m c : ℝ} (H0 : X.Sound H) (hS : X.stencil ⊆ S) {u : Form G} {x : Label G d}
    (h : Coin H F S b.order b o u x c) (hm : 1≤m) (hf : stipend H X b S o m) :
    ∀ U, ‖gap X (footprint S o) b.threshold o u (coat F b.threshold x) U‖ ≤ ((1+m)*c)*b.threshold⁻¹^d := by
  let v := coat F b.threshold x
  let u' := canonical X b.threshold v
  have hp : Coin _ _ _ _ _ _ u' x (m*c) := outfit h hm hf
  intro U
  have hz : 0≤c := h.body.nonneg
  have ho : ‖places o u U‖ ≤ _ := h.group (expandAt o U)
  have hx : b.threshold^0 ≤ b.threshold⁻¹^d := by rw [pow_zero]; exact one_le_pow₀ ((one_le_inv₀ b.threshold_pos).mpr b.threshold_le)
  by_cases he : Healthy b.threshold (footprint S o) U
  · have hg := soup X H0 h hS v |>.born U
    rw [show gap _ _ _ _ _ _ _=0 from not_not.mp (fun H => hg H he),norm_zero]; exact mul_nonneg (by positivity) (pow_nonneg (by have:=b.threshold_pos; positivity) _)
  unfold gap wages; rw [Pi.sub_apply, masked_ne _ _ _ _ he, add_zero]; apply (norm_sub_le ..).trans
  rw [add_mul, add_mul, one_mul]
  refine add_le_add ho ?_
  by_cases ht : Healthy b.threshold (X.footprint o) U
  · rw [masked_eq _ _ _ _ ht]; exact (write_unitpart X H0 b.threshold v (expandAt o U)) ▸
      (show ‖canonical X b.threshold v _‖ ≤ _ from hp.group (expandAt o U))
  rw [masked_ne _ _ _ _ ht, add_zero]
  exact ((norm_le_pi_norm v _).trans ((coeff_le v).trans h.weights)).trans <| le_trans
    (le_mul_of_one_le_left hz hm) (le_mul_of_one_le_right (by positivity) (by simpa using hx))

-- κ (not w) used in the cutoff. Numeric margins for one hop. Keep both card(Y) and exponent till chosen.
def silver (p : BudgetPoint) (Y : Support n) (m c : ℝ) := p.mass Y ((1+m)*c)
def sif (p : BudgetPoint) (Y : Support n) (m : ℝ) := 1+2*p.mass Y (1+m)
def inkage (p : BudgetPoint) (Y : Support n) (d : ℕ) (w κ : ℝ) :=
  p.threshold⁻¹^d * (Real.exp (Y.card*w)-1) ≤ κ

def kit (X : SectionData F) (S : Finset Cover) (t : ℕ) (o : Site n) {R : Rep G n} (D : Pad R.activities R.p) (u : Form G) (x : Label G d) : Baton F n :=
  let v := coat F R.p.threshold x
  (v, Pi.single t (germ_v X R.p.threshold o u v), D.lay (hop R.activities R.p (footprint S o) (gap X (footprint S o) R.p.threshold o u v)))
lemma kit_linear {V : Type*} [AddCommGroup V] [Module ℂ V] (x : V →ₗ[ℂ] Label G d)
    (u : V →ₗ[ℂ] Form G) (X : SectionData F) (S : Finset Cover) (t : ℕ) (o : Site n) {R : Rep G n} (D : Pad R.activities R.p) :
    IsLinearMap ℂ (fun v => kit X S t o D (u v) (x v)) := by
  have ha (v v') : gap X (footprint S o) R.p.threshold o (u (v-v')) (coat F R.p.threshold (x (v-v'))) = gap X (footprint S o) R.p.threshold o (u v) (coat F R.p.threshold (x v)) - gap X (footprint S o) R.p.threshold o (u v') (coat F R.p.threshold (x v')) := by
    simp_rw [map_sub]; exact gap_sub _ _ _ _
  let k (v : V) := kit X S t o D (u v) (x v)
  have hz (v v' : V) : k (v-v')=k v-k v' := by
    apply Prod.ext
    · dsimp only [k,kit]; simp only [map_sub]; rfl
    apply Prod.ext
    · ext1 i; change (Pi.single t _ : ℕ→Config G n→ℂ) i=(Pi.single t _ : ℕ → Config G n → ℂ) i-(Pi.single t _ : ℕ → Config G n → ℂ) i
      by_cases H : i=t
      · subst i; simp only [Pi.single_eq_same]; funext U
        simp only [germ_v,map_sub,(canonical_linear X _).map_sub,places, Pi.sub_apply,Function.comp_apply]; abel
      simp only [Pi.single_eq_of_ne H,sub_zero]
    funext i U; dsimp only [k,kit,Pad.lay,Prod.snd_sub,Pi.sub_apply]; rw [ha]
    split <;> simp [hop,Gas.tag,Pi.sub_apply,sub_mul]; split <;> simp
  constructor
  · intro a b; have ht := hz (a+b) b; rw [add_sub_cancel_right] at ht; exact (eq_sub_iff_add_eq.mp ht).symm
  intro v w; change k (v • w) = _; dsimp only [k]
  have hw (U : Config G n) : gap X (footprint S o) R.p.threshold o (u (v • w)) (coat F R.p.threshold (x (v • w))) U =
      v • gap X (footprint S o) R.p.threshold o (u w) (coat F R.p.threshold (x w)) U := by
    unfold gap wages germ_v; simp only [map_smul,Pi.sub_apply,Pi.smul_apply, (canonical_linear X _).map_smul]
    by_cases h : Healthy R.p.threshold (X.footprint o) U <;> by_cases h' : Healthy R.p.threshold (footprint S o) U <;>
      simp [*,places,smul_eq_mul, mul_sub,mul_add]
  apply Prod.ext
  · change coat F _ (x (v • w)) = v • _; rw [map_smul,map_smul]; rfl
  apply Prod.ext
  · ext1 i; change (Pi.single t _ : ℕ→Config G n→ℂ) i = v • ((Pi.single t _ : ℕ → Config G n → ℂ) i)
    by_cases ht : i=t
    · subst i; simp only [Pi.single_eq_same]; funext U
      simp only [germ_v,places, map_smul, (canonical_linear X _).map_smul, Function.comp_apply, Pi.sub_apply,Pi.smul_apply, smul_sub]
    simp only [Pi.single_eq_of_ne ht,smul_zero]
  funext i U; change D.lay (hop _ _ _ _) _ _ = v * D.lay (hop _ _ _ _) i U
  unfold Pad.lay
  split_ifs; unfold hop tag; rw [hw]; split_ifs <;> simp [mul_assoc]
  simp

lemma kit_starts (X : SectionData F) {S : Finset Cover} (t : ℕ) (o : Site n) {R : Rep G n}
    (D : Pad R.activities R.p) (f : Form G) (x : Label G d) (A : Stripe n) (hx : A t=footprint S o) :
    Pressed X (castAt A (kit X S t o D f x)) (footprint S o) t o R f :=
  ⟨hx,rfl,fun i U => D.staged _ U i⟩

-- Coin→testLinks when OUR chosen covering fits.
lemma Coin.vanish {f : Form G} {c : ℝ} (h : Coin H F S k b o f 0 c) (hh : FitsIn S n) :
    H.PiVanish d o (places o f) ∧ places o f 1=0 := by
  have hz (J : Jet G) (t : ℝ) : places o f (H.testLinks d o J t)=f (H.links d J t) := fromAbove h.localizes hh o _
  have he : H.PiVanish d o (places o f) := by
    intro J; dsimp only
    simp_rw [hz]; exact ⟨(h.reads J).1,fun i hi => ((h.reads J).2.2 i hi).trans (by simp)⟩
  refine ⟨he,?_⟩
  have hm := (he 0).2 0 (Nat.zero_le _)
  have h : H.testLinks d o 0 0=1 := by unfold Hol.testLinks; rw [H.flat]; rfl
  simpa [h] using hm
lemma Coin.as_ (O : Site n) {f : Form G} {x : Label G d} {c : ℝ} (h : Coin H F S b.order b O f x c) :
    b.Regular (footprint S O) (places O f) ∧ b.supBounds O (footprint S O) (places O f) c := by
  refine ⟨⟨placing h.localizes,(h.smooth.comp (show Continuous (expandAt O (K:=G.El)) by unfold expandAt; fun_prop)).measurable,
    fun k U => ?_, fun U _ => ?_, fun U _ A l hl => h.body.smooth.has hl.le U A⟩,h.body.nonneg,fun U hu l hl H => ?_⟩
  · unfold places; rw [Function.comp_apply, expandAt_gauge]; exact h.invariant _ _
  · exact ((show ContDiff ℝ ∞ (fun v => places O f (increment U v)) from h.body.smooth [] (Nat.zero_le _) U).of_le
      (WithTop.coe_le_coe.mpr le_top)).contDiffAt
  exact le_trans (h.body.bound l hl H U hu) (by simp)

lemma zeroPrice (p : BudgetPoint) (Y : Support n) (o : Site n) :
    p.Regular Y (0:Config G n→ℂ) ∧ p.supBounds o Y (0:Config G n→ℂ) 0 := by
  have hz : LeftBound p.order (p.dirBound o) (Healthy p.threshold Y) 1 ‖(0:ℂ)‖ (0:Config G n→ℂ) :=
    LeftBound.const zero_le_one (0:ℂ)
  exact ⟨⟨fun _ _ _ => rfl,measurable_const, fun _ _ => rfl,fun U _ => (show ContDiffAt ℝ (p.order:ℕ∞) _ _ from contDiffAt_const),
    fun U _ A l hl => hz.smooth.has hl.le U A⟩, le_rfl, fun U hu l hl H => (hz.bound l hl H U hu).trans_eq (by simp)⟩

lemma kit_pays {m w c κ σ C Λ δ : ℝ} {A : Stripe n} (hx : X.Sound H) {t : ℕ} (hp : X.stencil⊆S)
    (hS : ∀ i,o∈A i) (ha : A t=footprint S o) (D : Pad R.activities R.p) (hr : R.Lawful σ C Λ δ w)
    (hκ : inkage R.p (footprint S o) d w κ) (he : 0<κ)
    {u x} (h : Coin H F S R.p.order R.p o u x c) (hm : 1≤m) (hf : stipend H X R.p S o m) (hn : FitsIn S n) :
    let z := castAt A (kit X S t o D u x)
    let p := silver R.p (footprint S o) m c
    z.Format o H R ∧ z.remBound o R κ (p+p) ∧ p+p+F.coeffSize z.x ≤ sif R.p (footprint S o) m*c := by
  intro z p
  let Y := footprint S o
  let T := R.p.threshold
  let v := coat F T x
  have hz : Coin H F S R.p.order R.p o (u-canonical X T v) 0 ((1+m)*c) := by
    have hv := h.sub (outfit h hm hf); rw [sub_self] at hv; rw [add_mul,one_mul]; exact hv
  let f := gap X Y T o u v
  have ht := kit_starts X t o D u x _ ha
  have ho (i) : Kept R.p (R.activities.forced i) Y (z.forced i) := write_tag D (soup X hx h hp v) hr.labels.forced _
  have hh : z.support=A := rfl
  have hc := h.body.nonneg
  have he' := hz.body.nonneg
  have hP : 0≤p := mul_nonneg (Real.exp_pos _).le he'
  have hb : z.support t=Y := ha
  refine ⟨?_, ⟨p,p,hP,hP,le_rfl,he,?_,?_⟩,?_⟩
  · refine ⟨fun i => ?_,hS,fun i => ?_,fun i Hi => ?_, fun i => (ho i).allowed,
      fun i H => (ho i).carries H (show o∈footprint S o from ha ▸ hS t),fun i => (ho i).sym,fun i => (ho i).uses,fun i => (ho i).borel⟩
    · rw [show z.regular=_ from ht.charge]; by_cases hi : i=t
      · subst i; rw [Pi.single_eq_same,hb]; exact (hz.as_ _).1
      rw [Pi.single_eq_of_ne hi]; exact (zeroPrice _ _ o).1
    · rw [show z.regular=_ from ht.charge]; by_cases hi : i=t
      · subst i; rw [Pi.single_eq_same]; exact (hz.vanish hn).2
      rw [Pi.single_eq_of_ne hi]; rfl
    rw [show z.regular=_ from ht.charge]; by_cases hi : i=t
    · subst i; rw [Pi.single_eq_same]; exact (hz.vanish hn).1
    rw [Pi.single_eq_of_ne hi]; intro J; simp; exact contDiffAt_const
  · let g : ℕ → ℝ := Pi.single t ((1+m)*c)
    have hh (i : ℕ) (h : i≠t) : R.p.mass (z.support i) (g i)=0 := by simp [BudgetPoint.mass,g,h]
    have hv : R.p.mass (z.support t) (g t)=p := by unfold g; rw [hb,Pi.single_eq_same]; rfl
    refine ⟨g,⟨fun i => ?_,summable_of_ne_finset_zero (s:={t}) (fun i hi => hh i (by simpa using hi)),
      by rw [tsum_eq_single t hh, hv]⟩, fun i => ?_⟩
    · dsimp only; by_cases he : i=t
      · rw [he,hv]; exact hP
      rw [hh i he]
    rw [show z.regular=_ from ht.charge]; by_cases hi : i=t
    · subst i; rw [Pi.single_eq_same,hb]; simpa only [g,Pi.single_eq_same] using! (hz.as_ _).2
    rw [Pi.single_eq_of_ne hi]; simpa [g,hi] using (zeroPrice R.p (z.support i) o (G:=G)).2
  · obtain ⟨b,⟨H1,H2,H3⟩,H4⟩ := ink_tag D Y (gap_value hx hp h hm hf) hr.labels.boundK
    refine ⟨b,⟨H1,H2,H3.trans ?_⟩,H4⟩
    change R.p.mass Y (_*_) * _ ≤ _
    rw [BudgetPoint.mass,← mul_assoc, mul_assoc (Real.exp _ * _), mul_comm κ p]; exact mul_le_mul_of_nonneg_left hκ hP
  have Hv : F.coeffSize z.x ≤ c := h.weights
  unfold p silver sif BudgetPoint.mass
  linarith only [Hv]
end YM.WardBin
