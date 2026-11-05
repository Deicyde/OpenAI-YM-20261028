import YM.TraceExtension.Perfect.Desktop

/-!
# Root chart estimate on scalar, leave nonlinear bounds separate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Perfect
open Function Filter Matrix Lattice Precision Laurent Stationary Bloch Exterior Tree RG Wilson
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius
variable {c f:Side}{S:StepData c f}{G:Gauge}{p u:Clip}{M R:PathData G}{η α D:ℝ}
variable {F:Forest S.ratio}{ρ:Bid.Dir G c→AxisChart G F}{W:Matrix (Body 1 f) (Body 1 c) ℝ}
variable (h:Critical F p M ρ)(ht: S.patch.Branches S.kernel G)(t:S.Choices)(hv:Guessed F W ρ)
include h ht t hv
lemma smooth_plan : fderiv ℝ (fun x=> content ((liftedUp F W ρ x).1)) 0=uniformM W:=by
  ext1 x; let H:= soldier F W t ρ; let U := fun x=> content (liftedUp F W ρ x).1
  have he := soldier_known h ht t hv
  let L:= ContinuousLinearMap.fst ℝ (Link G f) (BaseSites G c)
  have hh : U=L ∘ H:=rfl
  change fderiv ℝ U 0 x=_
  rw [hh,fderiv_comp 0 L.differentiableAt ((soldier_diff h ht t).differentiableAt (by simp)),L.fderiv,show fderiv ℝ H 0=_ from he]; rfl

variable (F W ρ) in
def fresh (m:Site f)(x:Link G c):Joint G c f:= wages S (switchSite (uniformM (of (gaugePad W m (S.ratio.count.val+1))) x)) 1 (liftedUp F W ρ x)
variable (m:Site f)
omit ht t hv in
lemma fresh_thaw : Thaw (fresh F ρ W m) 0 := (liftedThaw h).wages S (Army.powG (v:=uniformM _) (uniformM _).contDiff.contDiffAt) (Army.park _ _)
omit ht t hv in
lemma fresh_zero : fresh F ρ W m 0=1:=by simp [fresh,lift_origin h]
lemma first_fresh : fderiv ℝ (fun x=> content (fresh F ρ W m x).1) 0=uniformM (of (fleece W (S.ratio.count.val+1) m)):=by
 let Y:= fresh F ρ W m
 let Q:= uniformM (G:=G) (of (gaugePad W m (S.ratio.count.val+1)))
 let I:=uniformM (G:=G) W
 have hh : Thaw Y 0:=fresh_thaw h m; have hx:Y 0=1:=fresh_zero h m
 let U:=liftedUp F W ρ; let L x:=content (U x).1
 have hp : Thaw U 0:=liftedThaw h; have hL: ContDiffAt ℝ ω L 0:= hp.1.logL (by unfold U;rw [lift_origin h]; rfl)
 have hU: U 0=1:=lift_origin h; have he : L 0=0:=by unfold L; rw [hU]; simp
 have hz := smooth_plan h ht t hv
 ext1 x; let z:= uniformM (G:=G) (of (fleece W (S.ratio.count.val+1) m)); let P (v : ℝ):= v • x
 have hP : Tendsto P (𝓝 0) (𝓝 0):=by simpa [P] using (ray_id x).continuousAt.tendsto
 apply HasDerivAt.unique (f:=fun a:ℝ=> content (Y (P a)).1) (Push.side _ ((hh.1.logL (show (Y 0).1=1 from congr_arg Prod.fst hx)).differentiableAt (by simp)) x) (ray_content (show (Y (P 0)).1=1 from by unfold P; rw [zero_smul,hx];rfl) _)
 let Y' (v:Link G c):= switchSite (Q v)
 let K'(v:ℝ):= Y' (P v)
 have hk(i): HasDerivAt (fun v=> G.mat (K' v i)) (G.colorMat (gaugeColor (Q x) i)) 0:=by unfold K' Y' P; simp_rw [map_smul]; exact ray_power ..
 have he' : HasDerivAt (L ∘ P) (I x) 0:= by rw [← (show fderiv ℝ L 0=I from hz)]; exact (Push.side L (hL.differentiableAt (by simp)) x)
 have hQ(i): HasDerivAt (fun v=> G.mat ((U (P v)).1 i)) (G.colorMat (edgeColor (I x) i)) 0:=by
    have ht: (fun v=> G.mat ((U (P v)).1 i))=ᶠ[𝓝 0] fun v=>G.mat (input _ _ (L (P v)) i):=by
      filter_upwards [hP.eventually ((show Tendsto (fun x=>(U x).1) _ (𝓝 1) from (show (U 0).1=1 from congr_arg Prod.fst hU) ▸ hp.1.cont.tendsto).eventually content_encodes)] with v hv
      exact congr_arg G.mat (congr_fun hv i).symm
    refine HasDerivAt.congr_of_eventuallyEq ?_ ht
    exact ray_swap (V:=fun u:Link G f=>G.mat (input G f u i)) ((Army.powL (v:=id) contDiffAt_id i).differentiableAt (by simp)) (ray_input (I x) i) (u:=fun v=>L (P v)) (by unfold P; rw [zero_smul,he]) he'
 intro i
 have ha := ray_gauged (u:=K') (U:=fun v=>(U (P v)).1) (by simp [K',Y',P]) hk (by simp [P,hU]) hQ i
 suffices hu : z x=I x-gradientA G f (Q x) by
      change HasDerivAt _ (G.colorMat (edgeColor (z x) i)) _; rw [hu]; exact ha
 funext j
 suffices hevv:∀ (j:Body 1 f) (l:G.ColorIndex), z x (j.1,j.2,l)= I x (j.1,j.2,l) -gradientA G f (Q x) (j.1,j.2,l) from hevv (j.1,j.2.1) j.2.2
 intro j l; rw [first_uniform]; let A:= parts G 1 (arm _ _ _ x) l; let U':=of (gaugePad W m (S.ratio.count.val+1))
 change (of (fleece W (S.ratio.count.val+1) m)*ᵥ A) j=(W *ᵥ A) j- (d 0 f *ᵥ (parts G 0 (arm _ _ _ (Q x)) l)) _
 rw [show parts G 0 (arm _ _ _ (Q x)) l=U' *ᵥ A from uniformC ..]; rw [mulVec_mulVec]
 rw [show of (fleece W _ m)= W-d 0 f*U' from rfl, sub_mulVec]; rfl

-- pose all increments as smooth field & pay through any stage budget
variable {X: Type}[NormedAddCommGroup X][NormedSpace ℝ X][FiniteDimensional ℝ X][CompleteSpace X]
variable {J:Config G f→ ℝ}{Y:Config G f→Link G f}
variable (F W ρ) in
def outing (m:Site f)(x:Link G c):= switchSite (uniformM (of (gaugePad W m (S.ratio.count.val+1))) x)*salute F W x
omit t h ht hv in
lemma fresco (x:Link G c): fresh F ρ W m x=wages S (outing F W m x) 1 (encamp F ρ x):=by
 unfold fresh; rw [liftedUp,wage_comp,one_mul];rfl
omit h ht hv t in
lemma out_flag (G:Gauge): Army (outing (G:=G) F W m) 0 ∧ outing (G:=G) F W m 0=1:=by
 refine ⟨?_,?_⟩
 · apply Army.mul (Army.powG (v:=uniformM (of (gaugePad W m (S.ratio.count.val+1)))) (uniformM _).contDiff.contDiffAt) (Army.powG (v:=uniformM (G:=G) _) (uniformM _).contDiff.contDiffAt)
 simp [outing,salute]
omit t ht hv in
lemma colors (hJ:Cleric J): inheritJ F ρ J ∘ input G c =ᶠ[𝓝 0] (J ∘ input G f ∘ fun x=> content (fresh F ρ W m x).1):=by
 have hp:= out_flag (F:=F) (W:=W) m G
 let X:= fresh F ρ W m
 have hZ: Tendsto (fun x=>(X x).1) (𝓝 0) (𝓝 1):=by
      rw [show (1:Config G f)=(X 0).1 from (congr_arg Prod.fst (fresh_zero h m)).symm]; exact (fresh_thaw h m).1.cont.tendsto
 refine inspire.trans ?_
 filter_upwards [hJ.jacket (Link G c) _ _ _ (camp_thaw h|>.1) (congr_arg Prod.fst (encamp_zero h)) hp.1 hp.2,hZ.eventually content_encodes] with x hx hX
 exact hx.symm.trans (by change J ((wages S _ 1 (encamp F ρ x)).1)=_; rw [← fresco m x]; exact congr_arg J hX.symm)
omit hv in
set_option maxRecDepth 8192 in
lemma port (hY:Cloaked Y)(hp:M.Bounds p η α D): inheritY F ρ t Y ∘ input G c=ᶠ[𝓝 0] fun x=> let U:=fresh F ρ W m x; shuttle S t U (input G c x) (Y (input G f (content U.1))):=by
 refine (inmate t).trans ?_
 let X:= fresh F ρ W m; have hX: Thaw X 0:=fresh_thaw h _; have h0:X 0=1:=fresh_zero h m; let A:=encamp F ρ
 have he:= out_flag (W:=W) (F:=F) m G; let g:= outing (W:=W) (F:=F) (G:=G) m
 filter_upwards [hY.jacket (Link G c) (fun x=> (encamp F ρ x).1) g (1:G.El) (camp_thaw h|>.1) (congr_arg Prod.fst (encamp_zero h)) he.1 he.2,(show Tendsto (fun x=>(X x).1) _ (𝓝 1) from (show (X 0).1=1 from congr_arg Prod.fst h0) ▸ hX.1.cont.tendsto).eventually content_encodes, Stationary.awake t hp hX (congr_arg Prod.fst h0) ht root_customs, Stationary.awake t hp (camp_thaw h) (congr_arg Prod.fst (encamp_zero h)) ht root_customs] with x ha hb hc hh
 have hg : Lattice.gauge (g x) (A x).1=(X x).1:= (congr_arg Prod.fst (fresco m x (F:=F) (W:=W) (ρ:=ρ))).symm
 have hf: X x=wages S (g x) 1 (A x):=fresco ..
 have hi := shuttle_turn t (input G c x) ht (g x) 1 hh (hf ▸ hc) (Y (A x).1)
 change shuttle _ t _ _ _=shuttle S t (X x) _ (Y (input G f (content _)))
 rw [hb, ← hg, show Y (Lattice.gauge (g x) (A x).1)=_ from ha]
 rw [← hf,gauge_one] at hi; rw [hi]; apply edgeColor.injective; funext i; rw [armor_at]; exact (G.adjoint_one ..).symm
end YM.Trace.Perfect
