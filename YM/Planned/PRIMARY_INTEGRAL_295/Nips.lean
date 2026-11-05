import YM.Planned.PRIMARY_INTEGRAL_295.Sextants
/-!
# From real chart D rows at V=1 to literal xCut/sunup

Includes comparison first-order of I row with Q in own connector,
retaining harmonic sector. F0 derivatives from Sextants receipts.
All comparisons unaffected no-hole; assumes income.bounds not earning
those sector ancestry assertions. -/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Nips
open Function Filter Set Metric
open Labels Lattice RG Wilson Pressure Precision Exterior Tree Streets Carrier Bloch Place Next.Fluctuations
open Villa Fizz Fizz.Gush Bazaars Cedar  Oval
open Bunks Little Work.F01 Little.Core Push.Uniform Honey Drupes Density Mowing Festoons Work.F03 Xacts Sextants
open Bid (pulled bills Sworn stretch)
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius RealInnerProductSpace Classical
variable {G : Gauge} {c f : Side} {S:StepData c f}
variable (K:Core G S) (s:Signed) (a : Temps G f) (v:Dir G c) {Q:Teller G} (h:Teller.Funds Q S K.tube)

section
omit a v s K in
lemma scrap (s:Slot)(U:Config G f)(x:Site f): kink s 1 U x=G.curvature (faceValue U (slotFace s x)):=by
   unfold kink faceValue; rw [travel_at,travel_at,map_zero,zero_add,show travel (1:Config G f) x s.walk=1 from ?_,G.adjoint_one];
   · rfl
   rw [← (link_one (G:=G))]; exact Push.stroll_zero ..

include h

lemma fares (p:Twin f): K.note (s,.inl p) 0 a=cutX K.tube.high K.tube.up (pulled (K.reachable a) s) 1 K.R p := by
   let L:= bowed K s; let f':=K.jump (s,.inl p) 0; let U:=K.tube.up; let B:=K.tube.high
   have he (x:Cell f): ContDiffAt ℝ ω (fun a:Temps G f=>G.curvature (faceValue (K.seek s 0 a) x)) 0:=by -- f Side shadow
      apply curvature_diff_mat (u:=fun y=>_); simp_rw [Sextants.spout K s]
      exact (show ContDiffAt ℝ ω (fun v:Dir G f=> G.mat (faceValue (represent v) x)) (L 0) from by rw [map_zero]; apply Push.writes).comp _ L.contDiff.contDiffAt
   rcases p with ⟨p,b⟩; cases b
   · let q:=fun a:Temps G f=>Pressure.shoot B (K.seek s 0 a) p
     have hA: ContDiffAt ℝ ω q 0:= (he p).const_smul (Real.sqrt B.direct)
     apply HasDerivAt.unique (Push.side q (hA.differentiableAt (by simp)) a)
     unfold q; simp_rw [Sextants.births K s]; exact (curvature_of_hasDerivAt (face_deriv p (L a))).const_smul (Real.sqrt B.direct)
   obtain ⟨X,Y,hF,hY⟩:= h.feeds
   have hp' : U.Bounds K.tube.high Q.top.width Q.top.paths X:= h.high.symm ▸ hF
   let g (i:Slot)(y:Temps G f):=chip U p.2 i • G.curvature (faceValue (K.seek s 0 y) (slotFace i p.1))
   let A:=garth 1 K.R
   have hf : f'=fun y=>∑ i∈A,g i y:= by
      ext1 y; change K.etched s 0 y (p,true)=_
      rw [etched,if_pos rfl,Festoons.clipped_mb U hp' K _ _ p rfl]; simp only [seek_zero,clamp,scrap]; rfl
   have hv:ContDiffAt ℝ ω f' 0:= by rw [hf]; apply ContDiffAt.sum; intro i _; exact (he _).const_smul (chip U p.2 i)
   apply HasDerivAt.unique (Push.side f' (hv.differentiableAt (by simp)) a)
   change HasDerivAt (fun t=> f' (t • a)) (∑ i∈A,chip U p.2 i • faceCurl (slotFace i p.1) (L a)) 0
   rw [hf]; unfold g; simp_rw [births K s]
   exact HasDerivAt.fun_sum (fun i _=> (curvature_of_hasDerivAt (face_deriv (slotFace i p.1) (L a))).const_smul (chip U p.2 i))

lemma tans (p:Bond c): K.note (s,.inr p) 0 a = -Real.sqrt S.kernel.penalty • bills S (pulled (K.reachable a) s) (pole p):=by
   let k:=Push.SectorMeasure.Oriented.choice s K.k; let L:= bowed K s
   let V:=fun v:Dir G f=> G.mat (S.prediction (represent v) k p); let B:=S.kernel.penalty
   let F:=fun v:Dir G f=> -Real.sqrt B • G.plog (V v)
   have hp : S.patch.Branches S.kernel G:= h.knobs.symm ▸ h.kernel
   have he:K.jump (s,.inr p) 0=F ∘ L:=by
      ext1 a; unfold Core.jump; simp only [Sum.elim_inr]; unfold Core.conf Little.Core.target
      rw [seek_zero,Push.settled S hp,Sextants.spout,inv_one,mul_one]; rfl
   have hv: V 0=1:=by unfold V; rw [link_one,Push.settled S hp,G.mat_one]
   have hf : ContDiffAt ℝ ω F (L 0):=by
      rw [map_zero]; exact ((hv.symm ▸ G.plog_diff : ContDiffAt ℝ ω G.plog (V 0)).comp _ (Push.prediction_cont S hp p k)).const_smul (-Real.sqrt B)
   unfold Core.note; rw [he]; apply (Push.side (x:=a) (F ∘ L) ((hf.comp _ L.contDiff.contDiffAt).differentiableAt (by simp))).unique
   let v:=bills S (L a) (pole p)
   have hc : HasDerivAt (fun t:ℝ=> V (L (t • a))) (G.colorMat v) 0 :=by simp_rw [map_smul]; exact Push.prices S hp p k (L a)
   have hd:=((G.plog_diff.differentiableAt (by simp)).hasFDerivAt).comp_hasDerivAt_of_eq (x:=(0:ℝ)) hc (by simp only [zero_smul,map_zero,hv])
   exact (hd.congr_deriv (Place.plog_velocity ..)).const_smul (-Real.sqrt B)
end

def tileF (x:Twin f):= let b' := pulled (K.outPeak v a) s
    cutX K.tube.high K.tube.up b' 1 K.R x - Pressure.zip (K.tube.Φ K.R 1) (xcopeLin K s v) x

def tileI (x:Bond c):= zLin S (pulled (K.outPeak v a) s) (pulled v s) x - Pressure.zip (K.tube.Φ' K.R 1) (xcopeLin K s v) x

include h
lemma precise (i:Twin f ⊕ Bond c) (j:G.ColorIndex):
    let e: Seats G c f:=((s,i),j)
    (K.D 0).mulVec a e + fderiv ℝ (fun v=>K.F0 v e) 0 v = ballast * ((Sum.elim (tileF K s a v) (tileI K s a v) i) j):=by
   intro e; rw [token K s v h i j, Little.Core.D_mul,←mul_add]; apply congr_arg (ballast *·)
   apply (show K.note _ _ _ _+_=(K.note e.1 0 a + Sum.elim (sheerF K s v) (sheerI K s v) i) j from rfl).trans -- add space
   apply congr_arg (fun y:G.Color=>y j); cases i with
   | inl p=>
      change K.note (s,.inl p) 0 a+ sheerF K s v p = tileF K s a v p
      unfold tileF sheerF; unfold Core.outPeak; dsimp only
      rw [fares K s a h,combined,cutX_add]; abel
   | inr p=>
      change K.note (s,.inr p) 0 a+ sheerI K s v p = tileI K s a v p
      unfold tileI sheerI Core.outPeak; rw [tans K s a h,combined]
      have he(a b:Dir G f): bills S (a+b)=bills S a + bills S b:=by
         ext x y; unfold Bid.bills; simp only [parts_add,Matrix.mulVec_add,Pi.add_apply]; rfl
      let a':=pulled (K.reachable a) s; let b':=pulled (rustic (S:=S) v) s; let V:= pulled v s; let x:=pole p; let z:=Real.sqrt S.kernel.penalty
      have hg(A:Dir G f): zLin S A V p=z • (V x-bills S A x):=rfl
      rw [hg,hg,he,Pi.add_apply]; simp only [smul_sub,smul_add,neg_smul]; abel
end YM.Planned.PrimaryIntegral295.Nips
