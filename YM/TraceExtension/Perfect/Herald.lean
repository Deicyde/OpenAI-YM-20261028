import YM.TraceExtension.Perfect.Grant

/-!
# Combined contour view, at and before cut. One solver. -/
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Perfect
open Function Filter Matrix Lattice Precision Laurent Stationary Bloch Exterior Tree RG Wilson Finset
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {c f:Side} {S:StepData c f}{G:Gauge}{F:Forest S.ratio}{ρ:Bid.Dir G c→AxisChart G F}{W:Matrix (Body 1 f) (Body 1 c) ℝ}{p:Clip}{R:PathData G}
 {η β M:ℝ} {X:Config G f→ ℝ}{Y:Config G f→ Link G f}
section
variable (h:Critical F p R ρ)(hp:S.patch.Branches S.kernel G)(t:S.Choices)(hR:R.Bounds p η β M)
local notation "L"=>liftedUp F W ρ
include h
lemma fresh_lim (hX:Cleric X): (inheritJ F ρ X) ∘ input G c=ᶠ[𝓝 0] X ∘ input G f ∘ fun x=>content ((L x).1):=by
 let U:=liftedUp F W ρ; have hu: Thaw U 0:= liftedThaw h; have hv: U 0=1:= lift_origin h; let V:=encamp F ρ
 let k:= salute F W (G:=G)
 have he : Tendsto (fun x=>(U x).1) _ (𝓝 1):=(show (U 0).1=1 from congr_arg Prod.fst hv) ▸ hu.1.cont.tendsto
 apply inspire.trans
 filter_upwards [hX.jacket (Link G c) _ k 1 (camp_thaw h|>.1) (congr_arg Prod.fst (encamp_zero h)) (Army.powG (v:=uniformM _) (uniformM _).contDiff.contDiffAt) (by simp [k,salute];rfl),he.eventually content_encodes] with x hx hh
 exact hx.symm.trans (congr_arg X hh.symm)
include hp hR t
lemma mantle (hY:Cloaked Y): bottom (inheritY F ρ t Y)=ᶠ[𝓝 0] bottom Y ∘ stampA S t L:=by
 let f' : Acr G c→ Link G c:=fun x=> (bite G c x).1
 let U:= liftedUp F W ρ; have hu: Thaw U 0:= liftedThaw h; have hv: U 0=1:= lift_origin h; let V:=encamp F ρ
 let k:= salute F W (G:=G)
 have h': Tendsto f' (𝓝 0) (𝓝 0):=continuous_fst.continuousAt.tendsto.comp (show Tendsto (bite G c) (𝓝 0) (𝓝 0) from by simpa using (bite G c).continuous.tendsto 0)
 have he : Tendsto (fun x=>(U x).1) _ (𝓝 1):=(show (U 0).1=1 from congr_arg Prod.fst hv) ▸ hu.1.cont.tendsto
 suffices ht : inheritY F ρ t Y ∘ input G c=ᶠ[𝓝 0] fun x=> shuttle S t (U x) (input G c x) (Y (input G f (content ((U x).1)))) by
    filter_upwards [h'.eventually ht] with x hx
    unfold bottom stampA Function.comp; simp only [ContinuousLinearEquiv.apply_symm_apply]; rw [show inheritY _ _ _ _ _ = _ from hx]; rw [transposes,bill_pay]
 refine (inmate t).trans ?_
 have hx(i) v: armor (1:Coats G i) v=v:=by apply edgeColor.injective; funext b; rw [armor_at]; exact G.adjoint_one _
 filter_upwards [hY.jacket (Link G c) _ k 1 (camp_thaw h|>.1) (congr_arg Prod.fst (encamp_zero h)) (Army.powG (v:=uniformM _) (uniformM _).contDiff.contDiffAt) (by simp [k,salute];rfl),he.eventually content_encodes, Stationary.awake t hR hu (by rw [hv]; rfl) hp root_customs, Stationary.awake t hR (camp_thaw h) (congr_arg Prod.fst (encamp_zero h)) hp root_customs] with x hf hX h hV
 rw [hX, show Y (U x).1=_ from hf]; symm; rw [show U x=wages S (k x) 1 (V x) from rfl]; rw [show input G c x=Lattice.gauge (1:Coats G c) (input _ _ x) from (gauge_one _).symm, shuttle_turn t _ hp (k x) 1 hV h,hx]; simp [V,gauge_one]
end

-- pack scalar upper flux reader.
def ballX (J:Config G f→ℝ)(x:Acr G f):= J (input G f (bite G f x).1)
section
variable (hX:Cleric X)(h:Critical F p R ρ)(hp:S.patch.Branches S.kernel G)(t:S.Choices)
include hX h
lemma inn_letter (m:Site f): ballX (inheritJ F ρ X)=ᶠ[𝓝 0] ballX X ∘ stampA S t (fresh F ρ W m):=by
 let f': Acr G c→L[ℝ] Link G c:= ContinuousLinearMap.fst ℝ _ _ ∘L (bite G _).toContinuousLinearMap
 filter_upwards [(show Tendsto f' (𝓝 0) (𝓝 0) from by simpa using f'.continuous.tendsto 0).eventually (colors (W:=W) h m hX)] with x hx
 unfold ballX Function.comp stampA;simp only [(bite G f).apply_symm_apply]; exact hx
lemma moonset : ballX (inheritJ F ρ X)=ᶠ[𝓝 0] ballX X ∘ stampA S t (liftedUp F W ρ):=by
 let f': Acr G c→L[ℝ] Link G c:= ContinuousLinearMap.fst ℝ _ _ ∘L (bite G _).toContinuousLinearMap
 filter_upwards [(show Tendsto f' (𝓝 0) (𝓝 0) from by simpa using f'.continuous.tendsto 0).eventually (fresh_lim (W:=W) h hX)] with x hx
 unfold ballX Function.comp stampA;simp only [(bite G f).apply_symm_apply]; exact hx
end

lemma stampStanding (t:S.Choices)(H:Link G c→Stationary.Joint G c f)(h:S.patch.Branches S.kernel G)(hx:Thaw H 0)(hv:H 0=1): ContDiffAt ℝ ω (stampA S t H) 0:=by
 let U : Acr G c→L[ℝ] Link G c := ContinuousLinearMap.fst _ _ _ ∘L (bite G c).toContinuousLinearMap; have hy:=hx.1.logL (show (H 0).1=1 from congr_arg Prod.fst hv)
 have hh(j:Lines G f 1)(i:Lines G c 1): ContDiffAt ℝ ω (fun x:Acr G c=> shuttle S t (H (U x)) (input G c (U x)) (desk j) i) 0:=by
       apply contDiffAt_pi.mp (steering t h (fun x:Acr G c=> desk j) contDiffAt_const (Thaw.comp (w:=U) (g:=H) (?_) U.contDiff.contDiffAt) _ (Army.powL U.contDiff.contDiffAt))
       rotate_left; · rw [Function.comp_apply,map_zero,hv]
       rw [map_zero]; exact hx
 refine contDiffAt_pi.mpr fun j=>?_ ; cases j with
 | inl j=> apply contDiffAt_pi.mp (ContDiffAt.comp (g:=fun x=> content (H x).1) _ (map_zero U |>.symm ▸ hy) U.contDiff.contDiffAt)
 | inr j=> simp_rw [stamp_entry]; exact ContDiffAt.sum fun i _=> (hh j i).mul (by fun_prop)
end YM.Trace.Perfect
