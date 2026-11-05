import YM.FullVolume.Artes.Tail
/-! Promotion S solids: affine transfer unforced path D3, D4.V.Of Passive clips.Joint metric. All variants are actual real.Path life. -/
set_option autoImplicit false
noncomputable section
namespace YM.Stationary.Artes
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Supply
open Shade Beacon Flagship ConeRay Tralis WilsonStartup WilsonStartup.Change WilsonStartup.Change.Reading Next.Free Next.Free.Retort
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical InnerProductSpace
variable {G: Gauge}{a:Levels G} {s:Sheet G}{L: Rolls s}{Q:PostCost L}{O:ChartRatio G}{m:ℕ}
variable {F H W: Tale a m}{J : FaceRow}{V:ℕ→ Reel G}
lemma vertical_core {P P':PathData G}(he:P.row=P'.row)(p:Clip)(n:Side) : inputSeries (m:=n) p P=inputSeries p P':=by funext i; unfold inputSeries secondTerm quadratic PathData.ell PathData.ellTerms; rw [he]
-- affine sums Harmony
namespace Tale
variable (hf:F.Earns Q O V J)(hh:H.Earns Q O V J)(hw:W.Earns Q O V J)
set_option quotPrecheck false
local notation "p"=> (a.params (m+1)).clip
local notation "q"=> (a.params m).clip
-- input formula projection
private lemma lawn {n : Side} (V: Vow G 2)(x y z: Cameo G 2) (b:ℝ)(he:z=x+b • (y-x)):
     Knot (turnSeries (ringT V.δ x) (m:=n)) (turnSeries (ringT V.δ y)) (turnSeries (ringT V.δ z)) 0 2 b:=by
   let P:= fun «q»:Cameo G 2=> turnSeries (ringT V.δ «q») (m:=n);
   have h (u:Cameo G 2):Matches 2 (P u) (fun _=>0) 0:=by
        have hp:AnalyticAt ℝ (P u) 0:= shineN V.hired
        refine ⟨hp.contDiffAt,contDiffAt_const,fun i hi=>?_⟩; rw [(rays_jet hp 3).1 (turns_low _ (half_pos V.hired) (Shade.radius V.δ _ (half_lt_self V.hired) _ (le_refl _))) i (by omega)]; interval_cases i <;> simp
   refine ⟨(h x).trans (h y).symm,(h x).trans (h z).symm,?_⟩
   unfold sign; rw [← V.tells x n,← V.tells y n,← V.tells z n,he,map_add,map_smul,map_sub]
private lemma park4 {n:Side}(V:Vow G 3)(x:Cameo G 3): Matches 3 (turnSeries (ringT V.δ x) (m:=n)) (fun _=>0) 0:=by
   let F:=turnSeries (ringT V.δ x) (m:=n)
   have he:AnalyticAt ℝ F 0:= shineN V.hired
   refine ⟨he.contDiffAt,contDiffAt_const,fun i hi=>?_⟩
   rw [show iteratedFDeriv ℝ i (turnSeries _) _= 0 from (rays_jet he _).1 (turns_low _ (half_pos V.hired) (Shade.radius V.δ _ (half_lt_self V.hired) _ (le_refl _))) i (by omega)]
   interval_cases i <;> simp
private lemma laughter {n:Side}(V:Vow G 3)(x y z:Cameo G 3)(b:ℝ): Knot (turnSeries (ringT V.δ x) (m:=n)) (turnSeries (ringT V.δ y)) (turnSeries (ringT V.δ z)) 0 2 b:=by
    have he:= (park4 (n:=n) V x).trans (park4 V y).symm; have hp:= (park4 V x).trans (park4 (n:=n) V z).symm
    refine ⟨he.lower (by omega),hp.lower (by omega),?_⟩
    unfold sign; rw [← show sign _ _ (2+1)=_ from he.jets _ (by decide), ← show sign _ _ (2+1)=_ from hp.jets _ (by decide),sub_self,smul_zero,add_zero]
include hf hh hw
private lemma snapshot {c:Side}(u:ℝ)(h:F.input.row=H.input.row)(he:F.input.row=W.input.row)(hu:W.stock.b=F.stock.b+u • (H.stock.b-F.stock.b)): Knot (intended p F.input (m:=c)) (intended p H.input) (intended p W.input) 0 2 u :=by
    simp_rw [intent,← vertical_core h p c, ← vertical_core he p c,
         hf.arrives.2.1,hf.arrives.2.2,hh.arrives.2.1,hh.arrives.2.2,hw.arrives.2.1,hw.arrives.2.2]; exact ((Knot.constant (stain_knit F.input p hf.bounds|>.analytic.contDiffAt)).add (lawn (V (m+1)).e3 _ _ _ u hu)).add (laughter (V (m+1)).e4 ..)
private lemma lyric (u:ℝ){i t:ℕ}(hi:2≤t)(hI:t≤3)(U:Knot (intended p F.input (m:=a.S.side (m+1) i)) (intended p H.input) (intended p W.input) 0 t u):
   Knot (intended q F.receipts (m:=a.S.side m i)) (intended q H.receipts) (intended q W.receipts) 0 t u :=by
   let S:=a.clock.op m i; let f:= treeQ a m i; let k:=keyQ a m i
   obtain ⟨hA,hB,hF⟩:= hf.score _ f; obtain ⟨-,hC,hX⟩:= hh.score _ f; obtain ⟨-,hD,hY⟩:= hw.score _ f -- hX,.. jets ≤4. need param t ≤3
   let Vx := fun a:VChart G f=> readFine f a; obtain ⟨x,hx,h,hv⟩:= Beacon.reverse_run Vx (readFine_one _) (readFine_diff _)
   have hT : Knot (mainTerm p F.input ∘ Vx) (mainTerm p H.input ∘ Vx) (mainTerm p W.input ∘ Vx) 0 t u:=by
       rw [← hx] at U; exact (U.comp (Knot.constant h) (by omega)).dawn (hv.fun_comp (mainTerm p F.input)) (hv.fun_comp (mainTerm p H.input)) (hv.fun_comp (mainTerm p W.input))
   let V' (x:VChart G f):=noiseTaylor S (represent x.1) (Vx x) k
   have hx : ContDiffAt ℝ ω V' 0 :=by rw [show V'=onSlice f k p F.input-mainTerm p F.input ∘ Vx from funext fun i => (add_sub_cancel_left ..).symm]; exact (hB.2.2 k).1.sub hT.equal.left
   have hz: Knot (onSlice f k p F.input) (onSlice f k p H.input) (onSlice f k p W.input) 0 t u:=hT.add (Knot.constant hx)
   cases t with
   | zero=>omega
   | succ t=>
    obtain ⟨-,hJ⟩ := braided (definite_of hA (Q.price _) k (hB.2.2 k).1) hz (station_of hB k) (station_of hC k) (station_of hD k) (by omega)
    let L:=arm G (a.S.side m i) 1
    suffices HE:Knot (mainTerm q F.receipts ∘ represent (n:=a.S.side m i)) (mainTerm q H.receipts ∘ represent) (mainTerm q W.receipts ∘ represent) 0 (t+1) u by rw [← L.map_zero] at HE; exact HE.comp (Knot.constant L.contDiff.contDiffAt) (by omega)
    let g(T:Tale a m):= (mainTerm q T.receipts)∘ represent (n:=a.S.side m i)
    let Z(T:Tale a m):= (onSlice f k p T.input) ∘ (WilsonStartup.Change.graph (T.Ψ i f))
    have hm (T:Tale a m)(hp:T.Earns Q O V J) : Matches (t+1+1) (g T) (Z T) 0:=by
         have hr:= (hp.score i f).2.2
         refine ⟨(hr 0 (by decide) k).2.1,(hr 0 (by decide) k).1,fun j hj=> (hr j (by omega) k).2.2.symm⟩
    refine ⟨((hm F hf).lower (by omega)).trans (hJ.equal.trans ((hm H hh).symm.lower (by omega))), ((hm F hf).lower (by omega)).trans (hJ.credit.trans ((hm W hw).symm.lower (by omega))),?_⟩
    change sign (g W) 0 _ = sign (g F) _ _ + u • (sign (g H) _ _-sign (g F) _ _); unfold sign; rw [(hm W hw).jets _ le_rfl,(hm F hf).jets _ le_rfl,(hm H hh).jets _ le_rfl]
    exact hJ.shift
omit hf hh hw in
private lemma cue (T:Tale a m)(hw:T.Earns Q O V J)(x:Side)(j:ℕ): let P:=T.receipts; iteratedFDeriv ℝ j (intended q P (m:=x)) 0=iteratedFDeriv ℝ j (inputSeries q P) 0 + iteratedFDeriv ℝ j (turnSeries (ringT (V m).e3.δ T.sold.b)) 0 + iteratedFDeriv ℝ j (turnSeries (ringT (V m).e4.δ T.sold.c)) 0:=by
    dsimp only; have hb : ContDiffAt ℝ j (inputSeries q T.receipts (m:=x)) 0:= (stain_knit _ q hw.out).analytic.contDiffAt
    have hv : ContDiffAt ℝ j (turnSeries (ringT (V m).e3.δ T.sold.b) (m:=x)) 0:= (shineN (V m).e3.hired).contDiffAt
    have ht : ContDiffAt ℝ j (turnSeries (ringT (V m).e4.δ T.sold.c) (m:=x)) 0:= (shineN (V m).e4.hired).contDiffAt
    rw [intent,hw.goes.2.1,hw.goes.2.2, iteratedFDeriv_add_apply (f:= inputSeries q T.receipts + turnSeries (ringT (V m).e3.δ T.sold.b)) (hb.add hv) ht,iteratedFDeriv_add_apply hb hv]

lemma swerves (u:ℝ)(h:F.input.row=H.input.row)(he:F.input.row=W.input.row)(hR:F.receipts.row=H.receipts.row)(hz:F.receipts.row=W.receipts.row)(hu: W.stock.b=F.stock.b+u • (H.stock.b-F.stock.b)): W.sold.b=F.sold.b+u • (H.sold.b-F.sold.b):=by
    let V':=(V m).e3.royal (a.S.side m); have hp:F.sold.b∈ V':= hf.shape.2.2.1; have hy : H.sold.b∈ V':= hh.shape.2.2.1
    refine (V m|>.e3).necessary (a.S.side m) hw.shape.2.2.1 (V'.add_mem hp (V'.smul_mem u (V'.sub_mem hy hp))) fun i=>?_
    have h:= lyric hf hh hw u (i:=i) (t:=2) le_rfl (by norm_num) (snapshot hf hh hw u h he hu); have hS:= h.shift; unfold sign at hS; let c:=a.S.side m i
    have hc (T:Tale a m): iteratedFDeriv ℝ (2+1) (turnSeries (ringT (V m|>.e4.δ) T.sold.c) (m:=c)) 0=0:= ((park4 _ _).jets _ le_rfl).trans (by simp)
    rw [cue F hf, cue H hh, cue W hw, ←vertical_core hR q c,←vertical_core hz q c,hc F,hc H,hc W] at hS
    simp only [add_zero,add_sub_add_left_eq_sub,←add_assoc] at hS
    rw [map_add,map_smul,map_sub,Vow.tells,Vow.tells,Vow.tells]; rw [add_assoc] at hS; exact add_left_cancel hS
omit hw in
lemma synchrony (h:F.input.row=H.input.row)(he:F.stock.b=H.stock.b)(hy:F.receipts.row=H.receipts.row): H.sold.b=F.sold.b:=by
    have hP:=swerves hf hf hh 0 rfl h rfl hy (by rw [he]; simp); simpa using hP
lemma parade (u:ℝ)(h:F.input.row=H.input.row)(he:F.input.row=W.input.row)(hR:F.receipts.row=H.receipts.row)(hz:F.receipts.row=W.receipts.row)(ha:F.stock.b=H.stock.b)(hb:F.stock.b=W.stock.b)(hu:W.stock.c=F.stock.c+u • (H.stock.c-F.stock.c)): W.sold.c=F.sold.c+u • (H.sold.c-F.sold.c):=by
    have hA:=synchrony hf hh h ha hR; have hB:=synchrony hf hw he hb hz; let V':=(V m).e4.royal (a.S.side m)
    refine (V m|>.e4).necessary (a.S.side m) hw.shape.2.2.2.2.1 (V'.add_mem hf.shape.2.2.2.2.1 (V'.smul_mem u (V'.sub_mem hh.shape.2.2.2.2.1 hf.shape.2.2.2.2.1))) fun i=>?_
    let d:=a.S.side (m+1) i; let R:= V (m+1) |>.e4
    have hp (X Y:Cameo G 3) := (park4 (n:=d) R X).trans (park4 R Y).symm
    have hK:Knot (intended p F.input (m:=d)) (intended p H.input) (intended p W.input) 0 3 u:=by
        rw [intent p F.input,intent p H.input,intent p W.input,←vertical_core h p d,←vertical_core he p d,hf.arrives.2.1,hf.arrives.2.2,hw.arrives.2.1,hw.arrives.2.2, hh.arrives.2.1,hh.arrives.2.2,← ha,← hb]
        refine (Knot.constant ((stain_knit F.input p hf.bounds (m:=d)).analytic.contDiffAt.add (shineN (V (m+1)).e3.hired |>.contDiffAt))).add ⟨hp ..,hp ..,?_⟩
        change iteratedFDeriv ℝ _ (turnSeries (ringT R.δ _)) 0=_; unfold sign
        rw [← R.tells W.stock.c d, ←R.tells F.stock.c d, ←R.tells H.stock.c d,hu,map_add,map_smul,map_sub]
    have hx:= (lyric hf hh hw u (i:=i) (by decide) le_rfl hK).shift
    let c:=a.S.side m i
    unfold sign at hx; rw [cue F hf, cue H hh, cue W hw,←vertical_core hR q c,← vertical_core hz q c,hA,hB] at hx
    simp only [add_sub_add_left_eq_sub,add_assoc] at hx -- order issue
    rw [map_add,map_smul,map_sub,Vow.tells,Vow.tells,Vow.tells]; first|exact add_left_cancel hx|exact add_left_cancel (add_left_cancel hx)
end Tale
end YM.Stationary.Artes
