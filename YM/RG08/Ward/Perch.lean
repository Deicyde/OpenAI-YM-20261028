import YM.RG08.Ward.Ice
import Mathlib.Analysis.Analytic.Order
/-! # Gauge retraction near this fixed torus, no bounded representatives.
Provides gauge invariant prolongation of jets AFTER the recurrence, not used
as a particular fixed stencil. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Reflect
open Filter MeasureTheory
open Function Analysis Tree Lattice RG Stationary Wilson Precision Exterior Laurent FreeResolvent Profiles Finset
open PertExtension.Series.Tested PertExtension.Series.Radial
open scoped BigOperators Topology Real ContDiff Classical Matrix.Norms.Frobenius
variable {c f n : Side} {G : Gauge}
variable {V W : ℝ→ Link G n} {Q : Pot G 2} {p : Air G}
lemma stretchable {E:Type} [NormedAddCommGroup E][NormedSpace ℝ E] {P : ℝ→ E} (h : AnalyticAt ℝ P 0)(hp : P 0=0) :
    ∃ v : ℝ→E,AnalyticAt ℝ v 0 ∧ ∀ᶠ t in 𝓝 0,P t=t • v t := by
  obtain ⟨v,hv,ht⟩:= (natCast_le_analyticOrderAt h (n:=1)).1 (by simp [_root_.Order.one_le_iff_ne_zero,(h.analyticOrderAt_ne_zero).2 hp]); exact ⟨v,hv,by simpa using ht⟩
lemma parts_arc (h : Beacon n p Q) (hd : Decked p)(he : Halt p) (hp : AnalyticAt ℝ V 0)(hz : V 0=0)
    (hy : AnalyticAt ℝ W 0) (hr : W 0=0) (hx : EquivalentNear V W) (k q : ℕ) :
    Fit (k+2+1) (grand (k+2) (sector Q p q) n ∘ V) (grand (k+2) (sector Q p q) n ∘ W) := by
  obtain ⟨v,hv,hb⟩:= stretchable hp hz; obtain ⟨w,hw,hh⟩:=stretchable hy hr
  have hp' := parts_beacon h hd he hv hw (hx.switch (EventuallyEq.symm hb) (EventuallyEq.symm hh)) k q
  exact (Fit.supply ((hb.filter_mono nhdsWithin_le_nhds).mono fun i hi=> congr_arg _ hi) _ |>.join hp' |>.join (Fit.supply ((hh.filter_mono nhdsWithin_le_nhds).mono (fun i hi=> congr_arg _ hi.symm)) _))

def walksNear (i : Site n) := route 0 (Lattice.lift i) default
lemma ending (i : Site n) : stop (0:Site n) (walksNear i)=i := by
  rw [← show wrap n 0=0 from map_zero _, ← wrap_stop_cover,walksNear,Lattice.route_end, wrap_lift]

def embassy (U : Config G n) (i : Site n) := travel U 0 (walksNear i)
lemma outset : embassy (1:Config G n)=1 := by
  funext i; unfold embassy; generalize walksNear i=W; change travel (1:Config G n) 0 W=1
  generalize (0:Site n)=x; induction W generalizing x with
  | nil=>rfl
  | cons d v ih=> unfold travel; rw [ih] -- hv remove
                  simp [Step.read]
lemma embassy_c : Continuous (embassy (G:=G) (n:=n)) := continuous_pi fun _=>continuous_travel _ _

def foyer (U : Config G n) := Lattice.gauge (embassy U) U
lemma foyer_c : Continuous (foyer (G:=G) (n:=n)) := by
  apply continuous_pi; intro i; unfold foyer Lattice.gauge; have hx:= embassy_c (G:=G) (n:=n); fun_prop
@[simp] lemma foyer_unit : foyer (1:Config G n)=1 := by unfold foyer; rw [outset,gauge_one]
lemma fixedSeat (U : Config G n)(k : Site n→G.El) : foyer (gauge k U)= gauge (fun _=> k 0) (foyer U) := by
  have hx v : embassy (Lattice.gauge k U) v=k 0 * embassy U v * (k v)⁻¹ := by rw [embassy,travel_gauge,ending]; rfl
  funext i; change embassy (Lattice.gauge k U) i.1 * Lattice.gauge k U i * _= _
  rw [hx,hx]; unfold foyer Lattice.gauge; group

lemma foyer_hol {x : Type} [NormedAddCommGroup x][NormedSpace ℝ x] {p : x→Config G n} (h : Army p 0) : Army (foyer ∘ p) 0 := by
  refine Army.slant (k:=embassy ∘ p) ?_ h; intro y
  suffices hh : ∀ (W:Walk) (u:Site n),ContDiffAt ℝ ω (fun z:x=> G.mat (travel (p z) u W)) 0 from hh (walksNear y) 0
  intro W; induction W with
  | nil=> exact fun _=> contDiffAt_const
  | cons k p ih=>
    intro u; simp only [travel]; apply ContDiffAt.mul _ (ih (u+ k.vec)); unfold Step.read; split; exact h.inv _; exact h _
-- uniform conjugates near unit need no choice of non-movable chart
lemma tents {X : Type*} {k : X→ Link G n} {z : X→G.El} {ℓ : Filter X}
    (h : Tendsto k ℓ (𝓝 0)) : Tendsto (fun p=> stain (z p) (k p)) ℓ (𝓝 0) := by
  have hx : Tendsto (fun p v=> G.adjoint (z p) ((arm G n 1 (k p)) v)) ℓ (𝓝 (0: fieldDir G n 1)) := by
    have hK : Tendsto (fun p=> arm G n 1 (k p)) ℓ (𝓝 0) := (((arm G n 1).continuous.tendsto' _ 0 (map_zero _))).comp h
    refine tendsto_pi_nhds.mpr fun i=> tendsto_zero_iff_norm_tendsto_zero.mpr ?_
    simp only [Gauge.norm_adjoint]; exact tendsto_zero_iff_norm_tendsto_zero.mp (tendsto_pi_nhds.mp hK i)
  exact ((arm G n 1).symm.continuous.tendsto' 0 0 (map_zero _)).comp hx
lemma contents_variable {X : Type*}{k : X→G.El} {p : X→Config G n}{ℓ : Filter X} (h : Tendsto p ℓ (𝓝 1)) :
    ∀ᶠ x in ℓ,content (Lattice.gauge (fun _=> k x) (p x))=stain (k x) (content (p x)) := by
  have hu:= (content_one (G:=G) (m:=n) ▸ (content_real G n).1.tendsto).comp h
  filter_upwards [(tents (z:=k) hu).eventually input_encodes,h.eventually content_encodes] with x hx hp
  simp only [Function.comp_apply] at hx; rw [← hx] -- carefully replacement
  exact congr_arg content ((congr_arg (Lattice.gauge (fun _=>k x)) hp.symm).trans (stain_cons ..))

section pro
variable (F : Link G n→ℝ) (h : ∀ U:G.El,∀ u,F (stain U u)=F u)
def suave (p : Config G n) := F (content (foyer p))
def statue (s : Signed)(p : Config G n) := suave F (pull s 0 p)
def resplendent (p : Config G n) := RG.Patch.average (fun s : Signed=> statue F s p)
include h
lemma suave_speaks {X : Type*} {k:X→ Coats G n} {U : X→Config G n} {ℓ : Filter X}(hv : Tendsto U ℓ (𝓝 1)) :
    ∀ᶠ x in ℓ, suave F (gauge (k x) (U x))=suave F (U x) := by
  have he:=contents_variable (k:=fun x=> k x 0) ((foyer_c.tendsto' 1 1 foyer_unit).comp hv)
  filter_upwards [he] with x hx; unfold suave; rw [fixedSeat]; erw [hx,h]; rfl
lemma pullers (s : Signed) {X : Type*} {k:X→ Coats G n} {U : X→Config G n}{ℓ : Filter X}(hv : Tendsto U ℓ (𝓝 1)) : ∀ᶠ x in ℓ, statue F s (gauge (k x) (U x))=statue F s (U x) := by
  have hu: pull s 0 (1:Config G n)=1 := by funext i; simp [rerun]
  have ht := suave_speaks F h (k:=fun x=> k x ∘ affine s 0) (((continuous_pull s 0).tendsto' 1 1 hu).comp hv)
  filter_upwards [ht] with u hu; unfold statue; rw [Work.F05.pull_gauge_zero]; exact hu
lemma glimmers {X : Type*}{k:X→Coats G n}{U:X→Config G n}{ℓ : Filter X}(hv:Tendsto U ℓ (𝓝 1)) : ∀ᶠ x in ℓ,resplendent F (gauge (k x) (U x))=resplendent F (U x) :=
    (eventually_all.mpr (fun i=> pullers F h i (k:=k) hv)).mono (fun _ hi=> congr_arg RG.Patch.average (funext hi))
omit h in
lemma statue_hol (s : Signed)(hp : ContDiffAt ℝ ω F 0) : ContDiffAt ℝ ω (statue F s ∘ input G n) 0 := by
  let z:Link G n → Config G n := pull s 0 ∘ input G n; have hZ : z=input G n ∘ orderTurn s := funext fun i=> flip_links ..
  have hz:Army z 0 := hZ.symm ▸ Army.powL (orderTurn s|>.contDiff|>.contDiffAt)
  have hu:z 0=1:= by rw [hZ]; simp
  have hP : (foyer ∘ z) 0=1:= by simp only [hu, Function.comp_apply, foyer_unit]
  exact (show ContDiffAt ℝ ω F (content ((foyer ∘ z) 0)) from (show content ((foyer ∘ z) 0)=0 by rw [hP]; exact content_one).symm ▸ hp).comp (f:=fun x=>content (foyer (z x))) 0 ((foyer_hol hz).logL hP)
omit h in
lemma revolvers (s : Signed) (x:Config G n) : resplendent F (pull s 0 x)=resplendent F x := by
  exact orbit_axis (suave F) x s
lemma shining (hp : ContDiffAt ℝ ω F 0) : Pointwise (resplendent F ∘ input G n) := by
  have hx: Tendsto (input G n) (𝓝 0) (𝓝 1) := by simpa using input_cont.tendsto (0:Link G n)
  refine ⟨(show ContDiffAt ℝ ω _ _ from ContDiffAt.mul contDiffAt_const (ContDiffAt.sum (s:=univ) (fun i _=> statue_hol F i hp))).analyticAt,fun s => Eventually.of_forall fun x=> ?_,fun z => ?_, ?_⟩
  · have hv : input G n (orderTurn s x)=pull s 0 (input G n x) := Eq.symm (flip_links ..)
    simp only [Function.comp_apply,hv]; exact revolvers ..
  · have he:= glimmers F h hx (k:=fun _ _=> z)
    filter_upwards [he] with x hh; rw [stain_cons] at hh; exact hh
  have hg:= glimmers F h (U:=fun x:Swatch G n=> input G n x.2) (k:=fun x=> switchSite x.1) (hx.comp (continuous_snd.tendsto (0:Swatch G n)))
  filter_upwards [hg,moveField_germ] with x hx he; simp only [Function.comp_apply]; rw [he]; exact hx
end pro
end YM.RG08.Reflect
