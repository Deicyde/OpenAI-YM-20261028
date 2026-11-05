import YM.TraceExtension.Sundial.Sieve
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Sundial
open Function Filter Set Extraction Climb Next.UVStress Table Work.A01 Maxwell UVNext.FreeStress Spin
open Spec Over Terrace MergeProof.East MeasureTheory Pilot
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius ContDiff Classical
variable {G:Gauge}{C:Family G}{X:Extraction.Order}
variable {S:Table C.book}(F: Final C X S)(H:(Bel C.book).Hierarchy)
local notation "F₀"=> Bel C.book
variable (h:G.Simple){𝓛:Ultrafilter (ℕ×ℕ)}{Z:Arch C} (hp:Bliss F 𝓛 Z H)
set_option quotPrecheck false
local notation "Act"=> (Bel C.book).Field 4
abbrev gum (C:Family G):Mat ((Bel C.book).Field 4):= LinearMap.toContinuousLinearMap (centering (Bel C.book) 4)
def peel(x y:ℝ): Mat Act := x • (spindle H h* gum C)+ y • (gum C-spindle H h*gum C)+(1-gum C)
lemma peels(x y:ℝ)(v:Act): peel H h x y v=x • spindle H h (gum C v)+ y • (gum C v-spindle H h (gum C v))+(v-gum C v):=rfl
include H in
lemma mint(x):gum C (gum C x)=gum C x:= zero_center (⟨_,center_lands H x⟩: Active (F₀))
include H
lemma morning(x):gum C (spindle H h (gum C x))=spindle H h (gum C x):= zero_center (⟨_,(show expectation (F₀) 4 _=0 from (pancake H h _).trans (center_lands H _))⟩: Active (F₀))
lemma halfcut(x y:ℝ)(v:Act): gum C (peel H h x y v)= x • spindle H h (gum C v)+ y • (gum C v-spindle H h (gum C v)):=by
    have hu (a:ℝ)(w:Act):gum C (a • w)= a • gum C w:= ((gum C).restrictScalars ℝ).map_smul ..
    rw[peels,map_add,map_add,map_sub,mint H,sub_self,add_zero,hu,hu,morning,map_sub,mint H,morning]
lemma spind(x y:ℝ)(v:Act): spindle H h (gum C (peel H h x y v))= x • spindle H h (gum C v):=by
    let s:=spindle H h; have hx(a:ℝ)(w:Act): s (a • w)=a • s w:= (s.restrictScalars ℝ).map_smul ..
    rw[halfcut,map_add,hx,hx,plinth,map_sub,plinth,sub_self,smul_zero,add_zero]
lemma cutover(x y:ℝ)(hx:x≠0)(hy:y≠0)(v:Act): peel H h x⁻¹ y⁻¹ (peel H h x y v)=v:=by
    rw[peels,spind,halfcut,peels,inv_smul_smul₀ hx, add_sub_cancel_left,inv_smul_smul₀ hy]; abel
lemma cutunit(x y:ℝ): peel H h x y ((F₀).unit 4)=(F₀).unit 4:=by rw[peels,show gum C ((F₀).unit 4)=0 from const_out H.laws];simp
lemma behave (x y) : ∀ (v:Act), expectation (F₀) 4 (peel H h x y v)=expectation (F₀) 4 v:=by
    intro v;let m:= (expectation (F₀) 4).restrictScalars ℝ; change m _=m _; rw[peels,map_add,map_add,map_sub,map_smul,map_smul,map_sub,show m (gum C v)=0 from center_lands H v,show m (spindle H h (gum C v))=0 from (pancake H h _).trans (center_lands H _)]; simp
lemma swerve(x y)(w: Ortho)(v:Act): (turns C).act _ w (peel H h x y v)= peel H h x y ((turns C).act _ w v):=by
    let f:= (turns C).act 4 w; let P:= f.toLinearMap; let m:= P.restrictScalars ℝ; have ht(z): gum C (f z)=f (gum C z):=by
       change centering (F₀) _ (f z)= f (centering (F₀) _ z); rw [value_center,value_center, expect_turn H (turns C) (Maxwell.Free.gear_motion _) z w,map_sub,map_smul,(baseRights (C:=C) (H:=H) h).identity]
    rw[peels,peels,ht];change m _=_; rw[map_add,map_add,map_smul,map_smul,map_sub,map_sub,show m (spindle H h _)=spindle H h (gum C v) from (paddleO H h _ _).1,(paddleO H h _ w).2];rfl
lemma smile(x y)(v:Act): (F₀).conj H.spin 4 (peel H h x y v)= peel H h x y ((F₀).conj H.spin 4 v):=by
    let m:= StressFlux.conjQ (d:=4) H.spin
    rw[peels,peels,show gum C ((F₀).conj H.spin 4 v)=(F₀).conj H.spin 4 (gum C v) from (conj_center H _).symm,realcat]; change m _=_;rw[map_add,map_add,map_smul,map_smul,map_sub,map_sub];rfl
include hp in
lemma mere(x y:ℝ): peel H h x y (stepField C)=x • stepField C:=by
    let v:=stepField C; have hv : gum C v=v:=zero_center (⟨v, sceneV H⟩:Active (F₀)); rw[peels,hv,riseS F H h hp]; simp only[v,sub_self,smul_zero,add_zero]
lemma vest(x y:ℝ)(a b:Axis): peel H h x y (standard4 C a b)=y • standard4 C a b:=by rw [peels,show gum C (standard4 C a b)=standard4 C a b from patch_s h a b,null_stress,smul_zero,sub_zero,sub_self,zero_add,add_zero]

lemma cut_linear(x y:ℝ)(hx:x≠0)(hy:y≠0): (peel H h x⁻¹ y⁻¹).toLinearMap.comp (peel H h x y).toLinearMap=LinearMap.id:= LinearMap.ext fun v=> cutover H h x y hx hy v
def elven(x y:ℝ)(hx:x≠0)(hy:y≠0): Act≃ₗ[ℂ] Act:= LinearEquiv.ofLinear (peel H h x y).toLinearMap (peel H h x⁻¹ y⁻¹).toLinearMap (by
      have he:= cut_linear H h _ _ (inv_ne_zero hx) (inv_ne_zero hy); rw[inv_inv,inv_inv] at he; exact he) (cut_linear H h _ _ hx hy)
lemma elven_symm(x y:ℝ)(hx:x≠0)(hy:y≠0)(v): (elven H h x y hx hy).symm v=peel H h x⁻¹ y⁻¹ v:=rfl
variable {u v:ℝ→ℝ}
lemma esprit (hp:Tendsto u trail (𝓝 1))(hq:Tendsto v trail (𝓝 1)): Tendsto (fun s=> peel H h (u s) (v s)) trail (𝓝 1):=by
    unfold peel; have ht:= ((hp.smul_const (spindle H h*gum C)).add (hq.smul_const (gum C- spindle H h*gum C))).add_const (1-gum C); simp only[one_smul,add_sub_cancel] at ht; convert! ht using 2
section
variable {K:S.Hierarchy}{P:change S 4}
lemma elder (g: AlignV F.room.kernel F.sector H P)(x y:ℝ)(hx:x≠0)(hy:y≠0): AlignV F.room.kernel F.sector H ((elven H h x y hx hy).trans P):=by
    constructor
    · refine ⟨fun v=>?_,?_,fun i k=>?_⟩
      · change P (peel _ _ _ _ _) = _; rw[← smile]; exact g.align.real _
      · change P (peel _ _ _ _ _) = _; rw[cutunit]; exact g.align.unit
      change P (peel _ _ _ _ _)= _; rw [← swerve]; exact g.align.axis ..
    intro v; rw [LinearEquiv.trans_apply,g.cent]; exact behave H h ..
end
end YM.Trace.Sundial
