import YM.Extension.UV.Station.AtomLimiter
import YM.Progress.JOINT_CALENDAR.Germs
set_option autoImplicit false
set_option maxHeartbeats 1300000
noncomputable section
namespace YM.Extension.UV.StationaryData
open Set Filter Function Lattice RG Wilson Precision Exterior Work.F02
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {G:Gauge} {m:Side} {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (B:E→ Config G m) {x:E} (hA: ContDiffAt ℝ ω (physical ∘ B) x) (hb:B x=1)
   (T:ℕ→PathData G) {p:Clip}{t A L:ℝ}(f:BookKey G→ℝ) (h:t>0) (ht:Tendsto (book_get ∘ T) atTop (nhds f)) (hT:∀ᶠ n in atTop,(T n).Bounds p t A L)
include hA h ht hT
lemma entity (k:Fin 3)(u:Site m)(b:Colors G k): Tracks ∞ (fun n y=>needle_report (book_get (T n)) u k b (physical (B y))) (fun y=>needle_report f u k b (physical (B y))) x:= (Tracks.unswerving (physical∘B) (hA.of_le le_top)).comply (needle_ball T f h ht hT (B x) u k b) (Eventually.of_forall (fun _=>rfl))
omit hA h ht hT in
lemma magnitude_receipt k f (hv:(book_path (G:=G) f).Bounds p t A L): Summable fun i=> (payload f k i).magnitude:= (Summable.of_nonneg_of_le (fun _=>by unfold Atom.magnitude; positivity) (fun i=> le_mul_of_one_le_right (by unfold Atom.magnitude; positivity) (Real.one_le_exp (show 0≤ t*(payload f k i).length by have hh:=hv.width; positivity))) (show Summable fun i=>(payload f k i).budget t by fin_cases k <;> first | exact hv.two.2.1 | exact hv.three.2.1 | exact hv.four.2.1))
set_option maxHeartbeats 700000 in
lemma uncut_limit (k:Fin 3): Tracks ∞ (fun n y=>uncut (payload (book_get (T n)) k) (B y)) (fun y=>uncut (payload f k) (B y)) x:=by
   haveI : NeZero (k.val+2):= ⟨by omega⟩
   unfold uncut
   apply Tracks.finset_sum _ _ _; intro y _
   have he:=Tracks.finset_sum (s:=Finset.univ) (fun b n x=>needle_report (book_get (T n)) y k b (physical (B x))) _ (fun b hb=>entity B hA T f h ht hT _ _ b)
   apply (he.linear Complex.reCLM).replace
   · filter_upwards [hT] with n hn
     funext z; exact (congr_arg Complex.re (needle_physical (x:=y) (h:=magnitude_receipt k _ (compact_bounds _ hn)) (B z))).symm
   exact funext fun z=>(congr_arg Complex.re (needle_physical (x:=y) (magnitude_receipt k _ (limit_bounds f T hT ht)) (B z))).symm
-- add summable magnitude helper
omit h hA hT ht in
private lemma ell_one (T:PathData G) (i:Face (Per m)): T.ell (1:Config G m) i=0:= by
   have he i (w:Walk): travel (1:Config G m) i w=1:=by induction w generalizing i with
      | nil=> rfl
      | cons a b h=> simp [travel,Step.read,h]
   have hp (b:Slot)(y:Site m): b.atSite (1:Config G m) y=0:=by simp only [Work.F03.atSite_path,he,faceValue,G.curvature_unit,map_zero]
   simp [PathData.ell,PathData.ellTerms,hp]

include hb
lemma matrix_limit : Tracks ∞ (fun n y=>quadratic p (compactify (T n)) (B y)) (fun y=>quadratic p (book_path f) (B y)) x:=by
   apply Tracks.finset_sum (s:=Finset.univ); intro u hu
   apply Tracks.add (Tracks.unswerving (fun y=>p.direct*G.price (faceValue (B y) u)) _)
   · apply (row_real T f h ht hT B (hA.of_le le_top) u).inline (fun v:G.Color=>‖v‖^2/2)
     · exact (contDiff_norm_sq ℝ).contDiffAt.div_const _
     rw [hb]; exact Eventually.of_forall fun _=>(ell_one _ _).trans (ell_one _ _ |>.symm)
   have he : ContDiffAt ℝ ω (fun y=>G.mat (faceValue (B y) u)) x:= by
      simp_rw [faceValue,← stringMat_physical]; exact (stringMat_contDiff (G:=G) _ _).restrict_scalars ℝ |>.contDiffAt.comp _ hA
   have hh : ContDiffAt ℝ ∞ (fun y=>G.price (faceValue (B y) u)) x:= ContDiffAt.of_le (contDiffAt_const.sub (((Complex.reCLM.comp ((Matrix.traceLinearMap (Fin G.repDim) ℝ ℂ).toContinuousLinearMap)).contDiff.contDiffAt.comp x he).div_const _)) le_top
   exact contDiffAt_const.mul hh
section zero
variable (hAt:∀ i, ContDiffAt ℝ ω (fun y=>G.mat (B y i)) 0) (hB:B 0=1)
include hAt hB
omit hb hA in
lemma main_limit: Tracks ∞ (fun n y=>mainTerm p (T n) (B y)) (fun y=>mainTerm p (book_path f) (B y)) 0 := by
   suffices e: Tracks ∞ (fun n y=>mainTerm p (compactify (T n)) (B y)) _ 0 from e.replace (hT.mono fun i hi=>funext fun b=>(intended_eq (T i) hi _).symm) rfl
   let V (s:Signed) (y:E):= pull s 0 (B y)
   have he s:= physical_contDiffAt (A:=V s) (G:=G) (fun i=>Progress.Joint.pulled_smooth B hAt s i) -- args
   let Q (M:PathData G) (s:Signed) (y:E):= quadratic p M (V s y)+uncut M.cubic (V s y) + uncut M.quartic (V s y)
   have he' s: V s 0=1:=by unfold V; rw [hB]; ext1 k; unfold pull Step.read; split <;> simp
   have hv s : Tracks ∞ (fun n=>Q (compactify (T n)) s) (Q (book_path f) s) 0:= ((matrix_limit (V s) (hA:=he s) (hb:=he' s) T f h ht hT).add (uncut_limit (V s) (hA:=he s) T f h ht hT 1)).add (uncut_limit (V s) (hA:=he s) T f h ht hT 2)
   exact ((Tracks.finset_sum (fun _ n=>_) _ Finset.univ (fun i hi=>hv i)).linear (((Fintype.card Signed:ℝ)⁻¹) • ContinuousLinearMap.id ℝ ℝ)).same rfl rfl
omit hb hA in
lemma secondary_limits : Tracks ∞ (fun n y=>loop (T n) (B y)) (fun y=>loop (book_path f) (B y)) 0 ∧ Tracks ∞ (fun n y=>secondTerm p (T n) (B y)) (fun y=>secondTerm p (book_path f) (B y)) 0 := by
   suffices e: Tracks ∞ (fun n y=>loop (compactify (T n)) (B y)) _ 0 ∧ Tracks ∞ (fun n y=>secondTerm p (compactify (T n)) (B y)) (fun y=>secondTerm p _ (B y)) 0 from ⟨e.1.replace (hT.mono fun i hi=>funext fun b=>(loop_eq (T i) hi _).symm) rfl,e.2.replace (hT.mono fun i hi=>funext fun b=>(second_eq (T i) hi _).symm) rfl⟩
   let V(s:Signed)(y:E):=pull s 0 (B y)
   have he s:= physical_contDiffAt (A:=V s) (G:=G) (fun i=>Progress.Joint.pulled_smooth B hAt s i)
   have he' s : V s 0=1:=by unfold V; rw [hB];ext1 k; unfold pull Step.read; split <;> simp
   let H := (((Fintype.card Signed:ℝ)⁻¹) • ContinuousLinearMap.id ℝ ℝ)
   exact ⟨((Tracks.finset_sum (fun _ n=>_) _ Finset.univ (fun i hi=> uncut_limit (k:=0) (hA:=he i) _ T f h ht hT )).linear H).same rfl rfl,((Tracks.finset_sum (fun _ n=>_) _ Finset.univ (fun i hi=> matrix_limit (V i) (he i) (he' i) T f h ht hT)).linear H).same rfl rfl⟩
end zero
omit hb hA in
lemma represent_limit : Tracks ∞ (fun n b=>mainTerm p (T n) (represent b)) (fun b=> mainTerm p (book_path f) (represent b)) (0:fieldDir G m 1) ∧
    Tracks ∞ (fun n b=> loop (T n) (represent b)) (loop (book_path f) ∘ represent) (0:fieldDir G m 1) ∧ Tracks ∞ (fun n b=> secondTerm p (T n) (represent (n:=m) b)) (fun b=>secondTerm p (book_path f) (represent b)) (0:fieldDir G m 1):= by
  have hp i:= (Work.F03.represent_smooth (G:=G) (n:=m) i).contDiffAt (x:=0)
  exact ⟨main_limit (E:=fieldDir G m 1) represent T f h ht hT hp link_one,(secondary_limits (E:=fieldDir G m 1) represent T f h ht hT hp link_one)⟩
end YM.Extension.UV.StationaryData
