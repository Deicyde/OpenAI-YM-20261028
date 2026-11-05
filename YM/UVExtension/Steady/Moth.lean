import YM.UVExtension.Steady.Pitch

/-! Buffer and raw crowns may not have angular smoothness on forced branches. Work
    with comparison values on those lanes. Distinguish Scroll "loft" conversion
    only for pure/unmarked readings. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Steady
open Filter Function Metric Set RG Lattice Pressure Wilson Precision Exterior Push.AbsoluteSums Finset ConnectedActivityE6
open Bloch Next.Fluctuations Blaze Channel SliceRows Work.E03 Work.F03 Reward Laurent Tree
open Pressure.Tube Pressure.Stores Scroll
open scoped BigOperators Topology InnerProductSpace ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{n c f:Side}{S:StepData c f} {ι α β κ:Type}{v:Filter ι}
namespace Concerted
variable {qq: Filter κ} {T:ι→ Tube G S}(p:Concerted v T) {t:κ→ Bool→ ι} (h:∀ b,Tendsto (fun n=> t n b) qq v)
variable {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {x:κ→ E} {k:ℕ} {d:ℝ} {U:κ→ E→ Config G f} {V:κ→ E→ Config G c}
variable (P:ℕ)(he:∀ᶠ i in qq,Mode (V i) (x i) k d)
variable (Q:κ→ S.Choices)(Y:κ→ Config G f)
include p h
omit p in lemma crownP {x:κ→ Config G n}(y: Cell n)(t':ℝ)(A:ι→ PathData G)(X:ι→ Clip)
  (Hp:∃ σ g,Revenues v σ A g)(Ht:∃ c,∀ i, X i=c)(D:ℕ)(hd:0<D): Together qq (fun i b=> crown (A (t i b)) (X (t i b)) P D t' (x i) y):=by
   obtain ⟨σ,g,H⟩:=Hp; obtain ⟨c',hc⟩:=Ht; simp_rw [crown,trunk,hc]
   have hx : Walt qq (fun (_:κ)=> (0:ℝ)) 0 (fun i b z=> if PathData.kept c' t' y.1 (x i) then ‖shorten (A (t i b)) P D (x i) y‖^2/2 else 0):=by
     let f i (_:ℝ):= x i
     have hV : ∀ᶠ n in qq,Mode (f n) 0 0 0:=Eventually.of_forall fun n=>⟨le_rfl,fun i=> a_oneB G (x n i) le_rfl⟩
     have hh:= media hV _ (fun b=> H.incurs (h b)) P D y hd
     exact Walt.choose (p:= (hh.plant (Z:=fun v:G.Color=> ‖v‖^2/2) (contDiff_norm_sq ℝ |>.div_const (2:ℝ))).excuse _) _ (Walt.ready _)
   apply hx.atProbe.add
   have hX := c'.quadratic_pos; have hY:= c'.tail_pos; let r:=c'.direct*2^2/2+c'.linear* |t'| *2
   let f i:= toll (x i) y
   have hr(i): ‖PathData.clipped c' t' (f i)‖≤r := by
      have he:0≤f i:= G.chord_nonneg _; have ht:f i≤2:=G.chord_le_two _; unfold PathData.clipped r; split
      next h0=> refine (le_add_of_nonneg_right (by positivity : 0≤c'.linear* |t'| *2)).trans' ?_; rw [Real.norm_of_nonneg (by positivity)]; gcongr
      next h0=> refine (le_add_of_nonneg_left (by positivity : 0≤c'.direct*2^2/2)).trans' ?_; rw [Real.norm_eq_abs,abs_mul,abs_mul,abs_of_pos hY,abs_of_nonneg he]; gcongr
   exact ⟨⟨r,Eventually.of_forall fun n _=> hr n⟩,(by simp [tendsto_const_nhds])⟩
include he
lemma canopyP (i:Twin f): Walt qq x k (fun n b y=> canopyF (T (t n b)) P (V n y) i):= Walt.schedule _ _ (fun j (_: j∈Finset.univ)=> p.reach h he _ j P true (p.xn h he P j))
lemma canopyJ (i:Bond c): Walt qq x k (fun n b y=> canopyI (T (t n b)) P (V n y) i):= Walt.schedule _ _ (fun j (_: j∈Finset.univ)=> extensionP h he p.qui _ _ P _ S.patch.L.property true (p.xn h he P j))
lemma canopyW (i:Co c Gain): Walt qq x k (fun n b y=> canopyN (T (t n b)) P (V n y) i):= Walt.schedule _ _ (fun j (_: j∈Finset.univ)=> extensionP h he p.ore _ _ P _ S.patch.L.property true (p.xn h he P j))
omit p h he
section extras
variable {a b: κ→Bool→ E→G.Color}
lemma radars (p:Walt qq x k a)(q:Walt qq x k b): Walt qq x k (fun i t y=> inner ℝ (a i t y) (b i t y)):= (p.both q).plant (contDiff_fst.inner ℝ contDiff_snd)
lemma selfP (p:Walt qq x k a): Walt qq x k (fun i t y=>‖a i t y‖^2/2):= p.plant ((contDiff_norm_sq ℝ).div_const (2:ℝ))
variable (W:κ→ E→ Config G c)
lemma zipper (he:∀ᶠ i in qq,Mode (W i) (x i) k d) (U:κ→Config G c)(j:Bond c):
    let f i y:= W i y j*(U i j)⁻¹
    Walt qq x k (fun n (_:Bool) y=> flaw (f n y)) ∧ Walt qq x k (fun n (_:Bool) y=> G.curvature (f n y)):=by
   intro f
   -- reuse Brush
   have hP : ∀ᶠ n in qq, Brush k (royalty G) d (fun y=> G.mat (f n y)) (x n):= by
       filter_upwards [he] with n hn; have h:= offsetB (u:=fun i=>W n i j) (hn.atLink j) 1 ((U n j)⁻¹); simpa only [one_mul] using! h
   refine ⟨?_, Walt.twin 1 d (hP.mono fun n hn=> ⟨Blaze.sculpt (g:=f n) hn,rfl⟩)⟩; -- price flaw via polynomial
   exact Walt.twin (flawBill G) (d+d) (by filter_upwards [hP] with i hi; exact ⟨cracked (f:=f i) hi, rfl⟩)
include he
lemma zipperZ (U:κ→ Config G c)(j:Bond c): Walt qq x k (fun n (_:Bool) y=> Tube.Z S (U n) (V n y) j):= Walt.pay (Walt.ready _) (zipper V he U j).2
omit he
end extras
include p h he
lemma stormP₁ (i:Cell c): Walt qq x k (fun n b y=> Scroll.stormL (T (t n b)) P (Y n) (S.prediction (Y n) (Q n)) (V n y) i):=by
    have hz : ∀ᶠ n in qq, Mode (fun (_:E)=> Y n) (x n) k 0:= Eventually.of_forall fun n=> ⟨le_rfl,fun j=> a_oneB G (Y n j) le_rfl⟩
    let σ:= fun i=> S.prediction (Y i) (Q i)
    unfold Scroll.stormL; apply Walt.schedule (κ:=Bool) _ _; intro w hw
    apply radars (p.xn h he P _)
    apply Walt.minus (q:=p.xn h he P _); apply Walt.sums; apply Walt.schedule univ _ (fun j hj=> p.reach h he _ _ P false (p.xf h hz P j)); exact Walt.schedule univ _ (fun j hj=> extensionP h he p.qui _ _ P _ S.patch.L.property false (zipperZ (S:=S) he σ j))
lemma stormP₂ (i:Cell c): Walt qq x k (fun n b y=> Scroll.stormD (T (t n b)) P (V n y) i):=by
   unfold Scroll.stormD; apply Walt.schedule univ _; intro w hw
   exact (radars (p.xn h he P (i,w)) ((p.xn h he P (i,w)).minus (((Walt.schedule univ _ (fun j hj=> p.reach h he _ _ P false (p.canopyP h P he j))).sums
      (Walt.schedule univ _ (fun j hj=> extensionP h he p.qui _ _ P _ S.patch.L.property false (p.canopyJ h P he j)))).sums (Walt.schedule univ _ (fun j hj=> extensionP h he p.ore _ _ P _ S.patch.L.property false (p.canopyW h P he j)))))).plant (Z:=fun i=>i/2) (contDiff_id.div_const _)
lemma lofty (z:ℝ)(u:Coat.Spot c f)(b:Bool): Walt qq x k (fun i n y=> Scroll.loft (T (t i n)) z (Y i) (Q i) (V i y) b u):=by
    let D:= Stores.till z; let K:=S.kernel.penalty; let L i:= S.prediction (Y i) (Q i)
    have hz : ∀ᶠ n in qq, Mode (fun (_:E)=> Y n) (x n) k 0:= Eventually.of_forall fun n=> ⟨le_rfl,fun j=> a_oneB G (Y n j) le_rfl⟩
    let Yf w:= p.xf h hz D w
    rcases u with i|i|i|i
    · cases b
      · exact (Walt.stamp (crownP h (x:=Y) D i _ (fun n=>(T n).up) (fun n=>(T n).high) p.cap p.high 1 (by decide))).sums (Walt.schedule _ _ (fun y hy=> (selfP (p.canopyP h D he (i,y))).minus (radars (p.canopyP h D he _) (Yf _))))
      obtain ⟨u,hu⟩:= p.high; change Walt qq x k (fun n b y=> (T (t n b)).high.direct*_+_); simp_rw [hu]
      have ht : Walt qq x k (fun i' b y=> flaw (faceValue (Y i') i)):=by
         exact Walt.twin (flawBill G) (0+0) (by filter_upwards with j; exact ⟨Blaze.cracked (a_oneB G _ le_rfl),rfl⟩)
      exact ((Walt.ready u.direct).times ht).sums (Walt.schedule _ _ (fun j _=> selfP ((Yf _).minus (p.canopyP h D he _))))
    · exact ((Walt.ready K).times ((zipper V he L i).1)).sums (selfP ((zipperZ (S:=S) he L _).minus (p.canopyJ h D he _)))
    · have hp : Walt qq x k (fun n (_:Bool) y=> flaw (faceValue (V n y) i)):=by
         let l:= (square i.2.val.1 i.2.val.2).length * (d*royalty G)
         exact Walt.twin (flawBill G) (l+l) (he.mono fun j hj=> ⟨Blaze.cracked (f:=fun y=>faceValue (V j y) i) (Blaze.tour _ _ hj.pos hj.atLink),rfl⟩)
      obtain ⟨u,hu⟩:= p.low; have hP: Walt qq x k (fun n b y=> stormC (T (t n b)) (V n y) i):=by simp_rw [stormC,hu]; exact (Walt.ready _).times hp
      exact hP.sums ((p.stormP₁ h D he Q Y i).sums (p.stormP₂ h D he i))
    exact selfP (p.canopyW h D he i)
end Concerted
end YM.UVExtension.Steady
