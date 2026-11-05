import YM.FullVolume.Artes.Deputy
/-! Promotion S solids: affine transfer unforced path D3, D4.V.Of Passive clips.Joint metric. All variants are actual real.Path life. -/
set_option autoImplicit false
noncomputable section
namespace YM.Stationary.Artes
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Supply
open Shade Beacon Flagship ConeRay Tralis WilsonStartup WilsonStartup.Change WilsonStartup.Change.Reading Next.Free Next.Free.Retort
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical InnerProductSpace
variable {G: Gauge}{a:Levels G} {s:Sheet G}{L: Rolls s}{Q:PostCost L}{O:ChartRatio G}{m:ℕ}
variable {F H W: Tale a m}{J : FaceRow}{V:ℕ→ Reel G}
-- affine sums Harmony
namespace Tale
variable (hf:F.Earns Q O V J)(hh:H.Earns Q O V J)(hw:W.Earns Q O V J)
set_option quotPrecheck false
local notation "p"=> (a.params (m+1)).clip
local notation "q"=> (a.params m).clip
-- input formula projection

private lemma enchant {n:Side}(K: Config G n)(V:Vow G 1)(R P Q:PathData G)(x y v:Cameo G 1)(u:ℝ)(h:R.loop=ringT V.δ x)(he:P.loop=ringT V.δ y)(ht:Q.loop=ringT V.δ v)(hp:v=x+u • (y-x)) : Precision.loop Q K= Precision.loop R K+u*(Precision.loop P K-Precision.loop R K):=by
   let f (C:Cameo G 1)(U:Config G n)(y:Site n)(i):=(ringT V.δ C i).unmasked U y
   have hs C U y: Summable (f C U y) := Summable.of_norm_bounded ((Shade.radius V.δ C V.hired _ (le_refl _)).2.1.mul_right (2^2)) (fun i=> by
       apply le_trans ((ringT V.δ C i).unmasked_bound U y); simp only [Atom.budget,zero_mul,Real.exp_zero,mul_one]; exact le_rfl)
   have hu (U:Config G n)(z:Site n): ∑' i,f v U z i = (∑' i,f x U z i)+u*((∑' i,f y U z i)-∑' i,f x U z i):=by
       rw [← (hs y U z).tsum_sub (hs x U z),←tsum_mul_left,←(hs x U z).tsum_add (((hs y U z).sub (hs x U z)).mul_left u) ]; refine tsum_congr fun i=>?_
       rw [hp]; simp [f, Atom.unmasked,Atom.poly,ringT, add_div, sub_div, Finset.mul_sum, ←Finset.sum_add_distrib,← Finset.sum_sub_distrib, mul_div_assoc,mul_add,mul_sub,add_mul, sub_mul,mul_assoc]
   unfold Precision.loop Patch.average uncut; simp_rw [ht,h,he];
   simp_rw [show ∀ j b,(∑' i,(ringT V.δ v i).unmasked (pull j 0 K) b)= _ from fun j b=>hu (pull j 0 K) b,Finset.sum_add_distrib,← Finset.mul_sum, Finset.sum_sub_distrib] -- sum_sub orientation
   unfold f; ring
include hf hh
private lemma iris (h:F.input.row=H.input.row)(ht:F.stock.b=H.stock.b)(hv:F.stock.c=H.stock.c)(i): let B:=treeQ a m i; let t:=keyQ a m i; onSlice B t p F.input = onSlice B t p H.input ∧ hessian B t p F.input=hessian B t p H.input ∧ F.Ψ i B=ᶠ[𝓝 0] H.Ψ i B:=by
    intro B t; obtain ⟨h₁,h₂,_⟩:= hf.score i B; have h₃:= (hh.score i B).2.1; let R:=F.input; let T:=H.input
    have he: tested B t p F.input=tested B t p H.input:=by
        unfold tested mainTerm quadratic PathData.ell PathData.ellTerms; rw [h,hf.arrives.2.1,hf.arrives.2.2,hh.arrives.2.1,hh.arrives.2.2,ht,hv]
    have hx: ContDiffAt ℝ ω _ (0:VChart G B) := (h₂.2.2 t).1; have hZ:= Change.definite_of h₁ (Q.price _) t hx
    refine ⟨congr_arg uncurry he,?_, Work.F05.station_unique (F:=tested B t p F.input) hx hZ.pos (h₂.1 ▸ h₂.2.1.continuousAt.tendsto) (h₃.1 ▸ h₃.2.1.continuousAt.tendsto) ((h₂.2.2 t).2.mono fun _ hi=> hi.fderiv) ?_⟩
    · unfold hessian; rw [he]
    rw [he]; exact (h₃.2.2 t).2.mono fun _ hi=> hi.fderiv
include hf hh hw
private lemma comet (hO:LocalRatio O)(u:ℝ)(h:F.input.row=H.input.row)(he:F.input.row=W.input.row)(hx:F.stock.b=H.stock.b)(hp:F.stock.b=W.stock.b)(hz:F.stock.c=H.stock.c)(hd:F.stock.c=W.stock.c)(hb:W.stock.a= F.stock.a +u • (H.stock.a-F.stock.a)):
      tick (a.S.side m) (W.steaming O)= tick _ (F.steaming O)+u • (tick _ (H.steaming O)-tick _ (F.steaming O)):=by
    funext i; let M := arm G (a.S.side m i) 1; let C:=treeQ a m i; let t:= keyQ a m i
    let U:= F.Ψ i C
    obtain ⟨h',hS,hU⟩:=iris hf hh h hx hz i; obtain ⟨ha,hV,hW⟩:=iris hf hw he hp hd i
    have hm: Tendsto M (𝓝 0) (𝓝 0):= M.map_zero ▸ M.continuousAt.tendsto
    let b:= F.steaming O i; let c:=H.steaming O i
    have heq : W.steaming O i =ᶠ[𝓝 0] b+u • (c-b):=by
         filter_upwards [hm.eventually hU,hm.eventually hW] with x hs hw'; change U _=H.Ψ i C (M x) at hs; change U _=W.Ψ i C (M x) at hw'
         let v:= U (M x); let K:= lifting C (represent (M x)) v
         let E(R:PathData G)(X:AxisChart G C):= Precision.loop R (lifting C (represent (M x)) X)+(1/2)*Real.log (hessian C t p R (M x) X).det - Real.log (∏ i,O.J (X i))
         change E W.input (W.Ψ i C (M x))= E F.input (U (M x))+u*(E H.input (H.Ψ i C (M x))-E F.input (U (M x)))
         rw [← hs,← hw']; unfold E; rw [← hV,← hS]; rw [show Precision.loop W.input _= _ from enchant K (V (m+1)).e2 F.input H.input W.input F.stock.a H.stock.a _ u hf.arrives.1 hh.arrives.1 hw.arrives.1 hb]; unfold K v; ring
    have hN (T:Tale a m)(h:T.Earns Q O V J): ContDiffAt ℝ (2:ℕ) (T.steaming O i) 0:= (show ContDiffAt ℝ ω (thermal C t p T.input (T.Ψ i C) O) (M 0) from M.map_zero.symm ▸ born h.bounds (h.score _ _|>.2.1) (h.score _ _|>.1) (Q.price _) hO t).comp _ M.contDiff.contDiffAt |>.of_le le_top
    change iteratedFDeriv ℝ 2 _ _= _; rw [(heq.iteratedFDeriv ℝ 2).self_of_nhds,iteratedFDeriv_add_apply (show ContDiffAt ℝ 2 b 0 from hN F hf) (show ContDiffAt ℝ 2 (u • (c-b)) 0 from ((hN H hh).sub (hN F hf)).const_smul u), iteratedFDeriv_const_smul_apply (show ContDiffAt ℝ 2 (c-b) 0 from (hN H hh).sub (hN F hf)), iteratedFDeriv_sub_apply (show ContDiffAt ℝ 2 c 0 from hN H hh) (show ContDiffAt ℝ 2 b 0 from hN F hf)]; rfl
lemma replay (x:G.ColorIndex)(hO:LocalRatio O)(u:ℝ)(h:F.input.row=H.input.row)(he:F.input.row=W.input.row)(hr:F.receipts.row=H.receipts.row)(ht:F.receipts.row=W.receipts.row)(hx:F.stock.b=H.stock.b)(hp:F.stock.b=W.stock.b)(hz:F.stock.c=H.stock.c)(hd:F.stock.c=W.stock.c)(hb:W.stock.a= F.stock.a +u • (H.stock.a-F.stock.a)):
   W.α=F.α+u*(H.α-F.α)∧ W.sold.a=F.sold.a+u • (H.sold.a-F.sold.a):=by
   let g(T:Tale a m):= (T.α:ℂ) • slots J G + filing T.receipts
   let M:= a.S.side m; have Ht (T:Tale a m)(H:T.Earns Q O V J): Tender T.pence (g T):= (H.average.coin T.α).patch (opB T.receipts q H.out M|>.1)
   have hk (T:Tale a m)(H:T.Earns Q O V J) : alphaPay x (g T)=T.α :=by
        obtain ⟨hp,hQ⟩:=opB T.receipts q H.out M; unfold g; rw [(H.average.coin _).weave hp,H.average.curated,H.salary,hQ]; ring
   let P:=W.pence-(F.pence+u • (H.pence-F.pence))
   have hP : Tender P (g W-(g F+(u:ℂ) • (g H-g F))):=(Ht W hw).minus ((Ht F hf).patch (((Ht H hh).minus (Ht F hf)).coin u))
   have hρ: tick M P=tick M W.pence - (tick M F.pence+u • (tick M H.pence-tick M F.pence)):=by
        have hx:=(Ht H hh).minus (Ht F hf); unfold P M; rw [(Ht W hw).ticked ((Ht F hf).patch (hx.coin _)),(Ht F hf).ticks (hx.coin _),hx.tickt,(Ht H hh).ticked (Ht F hf)]
   have hΨ := comet hf hh hw hO u h he hx hp hz hd hb
   have he : High M (tick M P):=by
       have hx := ((hf.highly).add (((hh.highly).sub (hf.highly)).coin u)).sub (hw.highly); rw [show tick M P=(F.prices O+u • (H.prices O-F.prices O))-W.prices O from ?_]; exact hx
       rw [hρ]; unfold Tale.prices; rw [hΨ]; unfold M; module
   obtain ⟨hx,hV⟩:= hP.marque (bound_climb ..) he x
   have hy:= (Ht H hh).minus (Ht F hf); rw [ (Ht W hw).void ((Ht F hf).patch (hy.coin u)), (Ht F hf).weave (hy.coin u), hy.curated,(Ht H hh).void (Ht F hf),hk H hh,hk F hf,hk W hw] at hV
   have ih:=sub_eq_zero.mp hV; let U:=(V m).e2; refine ⟨ih, U.necessary M hw.shape.1 ((U.royal M).add_mem hf.shape.1 ((U.royal M).smul_mem u ((U.royal M).sub_mem hh.shape.1 hf.shape.1))) fun i=> ?_⟩
   let F' := F.ancient
   have h1:H.ancient=F':=funext fun i=>(vertical_core hr q _).symm
   have h2 : W.ancient= F':=funext fun i=> (vertical_core ht q _).symm
   have hv(T:Tale a m)(H:T.Earns Q O V J)(hy:T.ancient=F'): tick M T.pence i = T.α • tick M F' i + U.freeze (M i) T.sold.a:=by
        have heq: tick M T.traceN i=U.freeze (M i) T.sold.a:=by
             rw [U.tells]; change iteratedFDeriv ℝ 2 (turnSeries T.receipts.loop) _= _; rw [H.goes.1]
        rw [← heq]; unfold pence; have hx := opB T.receipts q H.out M|>.1
        change tick M (_+T.traceN) i=_ ; rw [(H.average.coin T.α).ticks (show Tender T.traceN (filing T.receipts) from hx), H.average.tickt,hy]; rfl
   rw [hρ] at hx; have h := congr_fun hx i; change tick M W.pence i-(_ + u • (tick M H.pence i - tick M F.pence i))=0 at h
   rw [map_add,map_smul,map_sub]; rw [hv W hw h2,hv F hf rfl,hv H hh h1, ih] at h
   rw [add_smul,mul_smul,sub_smul] at h; simp only [smul_add,smul_sub] at *; linear_combination (norm:=abel) h -- fix
end Tale
end YM.Stationary.Artes
