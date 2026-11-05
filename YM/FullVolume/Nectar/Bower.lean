import YM.FullVolume.Nectar.Linos
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Muse.Veil
open Function Filter Set Lattice RG Pressure Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Animals
open MeasureTheory ProbabilityTheory Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Height Input Org Supply Pane Slide
open Push.PriceCompiler Progress.DirectedRecipe Jams Apse Empire Time Roof Chord Ovens
open FullVolume.Ray FullVolume.Urns FullVolume.Amp Pass Tent
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}{X:Metals G}{D:Rolls X.p}{A:Alloy X D}{R:Roost.Factor A}
variable {g:G.Simple}{v q d t t':ℝ}{N n m:ℕ}{L:Lyrics R t t}
open UniformSpace
set_option maxHeartbeats 480000
set_option synthInstance.maxHeartbeats 140000
variable (H:Chord R N m n t t){T:Team (stageP A.B.a (m+1) n)}
local notation "P"=> (stageP A.B.a (m+1) n)
local notation "Q"=> A.B.a.budget (m+1)
local notation "Ω"=> A.B.a.clock.hatBeta (m+1)
local notation "β"=> A.B.a.clock.hatBeta m
local notation "S"=> A.B.a.S.side (m+1) n
local notation "p_"=> Home T
/-! heterogeneous charter w Deck ler interpolation. Keep Home diameter.Mark Source.Generator not normalized Youth K.L.Sout.M.B. -/
abbrev Board (N m n:ℕ)(T:Team (stageP A.B.a (m+1) n)) := {t:Ticket A N m n // ∃ x : ℝ× Nilot T, ReadsF t x}
namespace Board
local notation "ι"=> Board (A:=A) N m n T
local notation "Γ"=> Weft T
abbrev wrap (t:ℝ × Nilot T):Weft T:=t
abbrev unveil (t: Weft T):ℝ × Nilot T:=t
variable (t₀:Board (A:=A) N m n T)(V:Climate (A.B.a.clock.hatBeta (m+1)))
abbrev globe (x:ℝ × Nilot T): Board (A:=A) N m n T:= if h:fromLambda Ω x.1∈band A.B.a (m+1)∧ ‖x.2‖≤1 then ⟨glades H x, ⟨x,gleans H _ h.1 h.2⟩⟩ else t₀
lemma glow (x:ℝ × Nilot T)(h:fromLambda Ω x.1∈band A.B.a (m+1))(hz:‖x.2‖≤1):ReadsF (globe H t₀ x).val x:=by unfold globe;rw [dif_pos ⟨h,hz⟩]; exact gleans H x h hz
variable {Y W' U: Type}[NormedAddCommGroup Y][NormedSpace ℝ Y] [CompleteSpace Y][SeminormedAddCommGroup W'][NormedSpace ℝ W'][NormedAddCommGroup U][NormedSpace ℝ U][CompleteSpace U]
variable {x: Weft T}{c:ℝ}(hp:choir q) (E:Board (A:=A) N m n T→W'→Y)
set_option quotPrecheck false
local notation "FQ" => fun f:sun→Board (A:=A) N m n T=> ∃ Y',SectorOn (A:=A) (fun i:sun=> (f i).val.val) Y'
variable (h : ∀ F:sun→Board (A:=A) N m n T, (∃ Y', SectorOn (A:=A) (fun i=> (F i).val.val) Y') → ∀ a b:W',(∀ t:sun,‖a+t.val • b‖≤1)→ Rebar (q/2) (phraseS (fun t=> E (F t) (a+t.val • b))) c)
include h V hp
lemma feeling (a:W')(ha:‖a‖≤1)(f:sun→Board (A:=A) N m n T) (hf: FQ f): Rebar (q/2) (phraseS (fun t=>E (f t) a)) c:=by simpa only [smul_zero,add_zero] using h f hf a 0 (by simpa only [smul_zero,add_zero] using fun _=>ha)
lemma sprungP (t:Board (A:=A) N m n T)(u:ℝ × Nilot T)(he : ReadsF t.val u)(hu:emcee Ω u.1)(a:W')(ha:‖a‖≤1): E t a=E (globe H t₀ u) a:=by
    have hv:=glow H t₀ u (he.takes ▸ t.val.val.property.2) he.norm
    let f(s:sun):= if s.val=0 then t else globe H t₀ u
    have h':= feeling V hp E h a ha f (trailP V (fun i=>(f i).val) u 0 hu (by change ‖(0:ℝ)‖ ≤ _; simp) (fun i=>by rw [smul_zero,add_zero]; unfold f; split_ifs;exact he;exact hv))
    have he:= Pass.unison h' (by linarith only [hp.1]) (b:=E (globe H t₀ u) a) (fun i hi=> congr_arg (fun x=> E x a) (show f i=_ from if_neg hi)); change E (f tip) a= _ at he;rw [show f tip=t from if_pos rfl] at he; exact he
local notation "ℋ"=> (Weft T)× W'
omit h V hp in
private lemma norms (x y: ℝ × Nilot T):‖wrap x- wrap y‖= max ‖x.1-y.1‖ ‖x.2-y.2‖:=by rfl
omit h V hp in
private lemma bar {hx wx:Nilot T}{u:sun}(hv:‖hx‖ ≤ 1/4)(ht: ‖wx‖≤1/4): ‖hx+u.val • wx‖≤1:= calc
   _ ≤ ‖hx‖+ ‖u.val • wx‖:= norm_add_le ..
   _ ≤ _:=by rw [show ‖u.val •wx‖= ‖u.val‖*‖wx‖ from norm_smul u.val (wx.val.val: Show (stageP A.B.a (m+1) n))]; exact (add_le_add hv ((mul_le_of_le_one_left (norm_nonneg _) (abs_le.mpr u.2)).trans ht)).trans (by norm_num)
local notation "xA" => (unveil x).1
local notation "uA" => (unveil x).2
variable (e:W'→L[ℝ] U) (hE:Isometry e)(hD:DenseRange e)
local notation "Θ"=> ContinuousLinearMap.prodMap (eT T) e
include hE hD H
omit h V hp H in
private lemma μPack : Isometry (ContinuousLinearMap.prodMap (eT T) e) ∧ DenseRange (ContinuousLinearMap.prodMap (eT T) e):= ⟨Isometry.prodMap (show Isometry (eT T) from (Guild.grouped T).1) hE,DenseRange.prodMap (show DenseRange (eT T) from (Guild.grouped T).2) hD⟩
local notation "tH"=> fun z:((Weft T) × W')=> E (globe H t₀ (unveil z.1)) z.2
private lemma themeP (hx:mild Ω xA)(hv:‖uA‖≤1/8): ∃ P':FullVolume.Amp.Pulse ((ℝ × Guild T)× U) Y (2*c),Hits (f:=fun y:(Weft T) × W'=> E (globe H t₀ (unveil y.1)) y.2) (ContinuousLinearMap.prodMap (eT T) e) (x,0) P':=by
    let x':=(x,(0:W')); obtain ⟨hz₁,hz₂⟩:= μPack (T:=T) e hE hD
    apply exitP _ x' hp hz₁ hz₂ le_rfl; refine ⟨by norm_num,?_⟩
    filter_upwards [Metric.closedBall_mem_nhds x' (show (0:ℝ)<1/8 by norm_num)] with z hy; intro u hw; rw [Metric.mem_closedBall,dist_eq_norm] at hy
    let y:= unveil z.1; let w:=unveil u.1
    have ht₀ : ‖z.2‖ ≤ 1/8:=by
        have hu:= (norm_snd_le (z-x')).trans hy; change ‖z.2-0‖ ≤ _ at hu;simpa using hu
    have hh : max |y.1-xA| ‖y.2-uA‖ ≤ 1/8:= (norms y (unveil x)).symm.trans_le ((norm_fst_le (z-x')).trans hy)
    have he' : max |w.1| ‖w.2‖ ≤ 1/4 := (norm_fst_le u).trans hw
    have hx₀:=Pass.samples V hx (((le_max_left ..).trans hh).trans (by norm_num));have ht:‖w.1‖≤1:=(le_max_left ..|>.trans he').trans (by norm_num)
    have hQ : ‖y.2‖≤1/4:= by have h:‖y.2-uA‖≤1/8:=(le_max_right ..).trans hh;linarith [norm_sub_norm_le y.2 uA]
    let f(s:sun):= globe H t₀ (y+s.val • w); refine Muse.roundTrip _ (h f (trailP V (fun i=> (f i).val) y w hx₀ ht (fun i=> glow H t₀ _ (Pass.band_full _ V hx₀ ht i) (bar hQ ((le_max_right ..).trans he')))) z.2 u.2 (fun i=>?_)) hp.1 -- infer.fun
    exact (norm_add_le ..).trans ((add_le_add ht₀ ((norm_smul i.val u.2).trans_le ((mul_le_of_le_one_left (norm_nonneg _) (abs_le.mpr i.property)).trans ((norm_snd_le u).trans hw)))).trans (by norm_num))
include t₀
lemma pulseS (f:sun→ Board (A:=A) N m n T)(y:sun→ ℝ × Nilot T)(u:sun→ W')(hf:∀ s:sun,mild Ω (y s).1)(hv:‖(y tip).2‖≤1/8)(hy:∀ s:sun,ReadsF (f s).val (y s))(X':Beam (ℝ × Guild T))(Z:Beam U)(hX:‖X'‖ ≤1/8)(hz:‖Z‖≤1/8)(hu:∀ s:sun,e (u s)=Beam.read _ s Z)(hY:∀ t:sun,Guild.groupB T (y t)=Guild.groupB T (y tip)+Beam.read _ t X'):∃ Z_:Beam Y, ‖Z_‖≤4*c∧∀ s:sun,E (f s) (u s)=Beam.read _ s Z_:=by
    let b:= (wrap (y tip),(0:W')); let p(i:sun):= (wrap (y i), u i); let Vg:= Θ; obtain ⟨P',hP⟩:= themeP H t₀ V hp E h e hE hD (x:=wrap (y tip)) (hf tip) hv -- order
    let W:= E (globe H t₀ (y tip)) (0:W'); let B' := Beam.lay X' Z
    have hr:‖B'‖≤1/4:= (Beam.layN ..).trans ((add_le_add hX hz).trans (by norm_num))
    obtain ⟨h₁,h₂⟩:= μPack (T:=T) e hE hD
    refine ⟨Beam.arm W+bead P' B',?_,fun s:sun=>?_⟩
    · have hs:=Pass.samples V (hf tip) (show |(y tip).1-(y tip).1| ≤2 by simp); let U0:= globe H t₀ (y tip); have ht:= (hy tip).norm
      have hF :‖W‖ ≤ c:= Pass.solo (feeling V hp E h (0:W') (by simp) (fun _=>U0) (trailP V _ (y tip) 0 hs (by change ‖(0:ℝ)‖≤_;simp) (fun i=>by rw [smul_zero,add_zero];exact glow H t₀ _ (Pass.simple_full _ V hs) ht))) tip
      have hc:0≤c:=(norm_nonneg _).trans hF
      exact (norm_add_le ..).trans ((add_le_add ((Beam.armN _).trans_le hF) (P'.liftN B' hr)).trans (by linarith))
    have hK: Vg (p s)-Vg b=Beam.read _ s B':=by
       rw [show _=_ from Beam.layL s X' Z]; refine Prod.ext ?_ ?_
       · change Guild.groupB T (y s) - Guild.groupB T (y tip)= Beam.read _ s X'; rw [hY s]; abel
       change e (u s)-e 0 = _; rw [map_zero, hu, sub_zero]
    have hs:‖p s-b‖≤1/4:=by rw [← dist_eq_norm,← h₁.dist_eq, dist_eq_norm]; change ‖Vg _-Vg _‖≤_; rw [hK]; exact (FullVolume.Amp.Beam.price B' s).trans hr
    have ht:= (show ‖e (u s)‖≤1 from ((hu s).symm ▸ ((FullVolume.Amp.Beam.price Z s).trans (hz.trans (by norm_num)))))
    have he:= sprungP H t₀ V hp E h (f s) _ (hy s) (Pass.samples V (hf s) (by simp)) (u s) ((hE.norm_map_of_map_zero (map_zero _) _).symm.trans_le ht)
    have hu : sees P' (Vg (p s)-Vg b)=E (globe H t₀ (y s)) (u s)-W:= hP.jingle (y:=p s) hs
    rw [map_add,Beam.armL, P'.liftL _ hr s, ← hK, hu]; rw [he]; abel
end Board
end YM.PhysicalNext.Repeat.Muse.Veil
