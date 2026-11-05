import YM.FullVolume.E6.Grails
/-! E6 Layout steps full volume.Epoch. Keep Records by exact tags.Canvas.Read.F. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Lim
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration PhysicalNext.Repeat Greenbelt Match Song Refrain
open Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open UVNext.CouplingReset Animals Progress.DirectedRecipe Ovens
open Stationary Stationary.Shade Stationary.Beacon Laurent Exterior Bloch
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {P : Teller G} {S : StepData c f} {F : Forest S.ratio}
open Matrix Window Progress.StationaryScenes Green Census Control Flux FullVolume.Shadow
open Gate Frond Vine Mask
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E] {φ: Filter ℕ}{J: Ultrafilter ℕ}{Q:ConnectedActivityE6.Target G P}{W x μ C₀ a b e ℓ v :ℝ}{o:Target.Order G W}
    {Λ: Era G S}{U:ℕ→ E→ Config G c}{Z: Draft F G} {K H:ℕ→ Epoch Λ}{j:ℕ}{p:E}
open Window Itinerary
variable {U U': ℕ→ E→ Matrix (Tubular f G) (Tubular f G) ℝ}{m n k :ℕ}{η r :ℝ} {κ:Type}
lemma Buds.sticky (b:Bond f)(i:Itinerary f k){D W:ℕ→ E→ℕ→ Itinerary.Mat f G}(h:∀ k:ℕ,Buds φ j p (fun n y=> D n y k) (fun n y=> W n y k)):Buds φ j p (fun n y=> combo b i (D n y)) (fun n y=> combo b i (W n y)) :=by
   induction k generalizing D W b with
   | zero=> unfold combo; exact fun i j=> Frill.still _
   | succ k ih=> simp_rw [combo]; refine Buds.pairs ?_ (ih _ _ (fun i=> h (i+1))); exact fun j k=> h 0 _ _
variable (h: Buds φ j p U U')(he: ∀ᶠ i in φ, Allow (U i p) (along (G:=G) S) m η r a)(hv: Torch η r a)
variable [φ.NeBot]
local notation "X₀"=> (Tubular f G → Tubular f G →ℝ)
private theorem liftP (A: E→Matrix κ κ ℝ) [Fintype κ]
    (h:∀ i k, ContDiffAt ℝ (↑ j) (fun y=> A y i k) p) (B:E→Matrix κ κ ℝ) (he:∀ i k, ContDiffAt ℝ (↑j) (fun y=> B y i k) p) (i k):
    ContDiffAt ℝ (↑j) (fun y=> (A y*B y) i k) p:=by simp_rw [Matrix.mul_apply]; exact ContDiffAt.sum fun j _=> (h i j).mul (he j k)
private theorem padP {κ:Type}{x':κ→Site c}(M:Window x' m)[Fintype κ] [DecidableEq κ](A:E→Matrix κ κ ℝ) (h: ∀ i k,ContDiffAt ℝ (↑j) (fun y=> A y i k) p) (he:(A p).PosDef)(i k):ContDiffAt ℝ (↑j) (fun y=> M.pad (A y) i k) p:=by
    by_cases hp : i∈ M.take k
    · simp_rw [Window.pad, Matrix.of_apply, dif_pos hp]; apply Blaze.jetBack (A:=fun y=> M.principal (A y) k) (fun i k=>h i k) (isUnit_iff_ne_zero.mpr ((he.submatrix Subtype.val_injective).det_pos.ne'))
    simp_rw [Window.pad, Matrix.of_apply,dif_neg hp]; exact contDiffAt_const
private theorem sculpture [FiniteDimensional ℝ E] {t:ℕ} (s:Bond f)(u: Itinerary f t)(Z:E→ℝ→ℕ→Itinerary.Mat f G)(h:∀ y∈Set.Icc (0:ℝ) 1,∀ l i k,ContDiffAt ℝ (↑j) (fun z:E×ℝ=> Z z.1 z.2 l i k) (p,y)):ContDiffAt ℝ (↑j :WithTop ℕ∞) (fun v=> stamp (Z v) s u) p:=by
   unfold stamp; refine ContDiffAt.sum fun _ j=>?_ ; simp_rw [checkIn, intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)]
   apply (Blaze.Meristem.calls (Blaze.yoga ?_)).1
   intro z hz; unfold uncurry; split
   · exact smooth_combo (fun x : E×ℝ=>Z x.1 x.2) (fun i hi=>h z hz _) u s _ _
   exact contDiffAt_const
include h he hv
private lemma shapes {g:X₀}(hp:Tendsto (fun i=> (U i p)) φ (𝓝 (Matrix.of g))) (z:ℝ)(hz:z∈Set.Icc (0:ℝ) 1): (glide (Matrix.of g) z).PosDef :=by
    exact Buds.assured (he.mono fun i hi=> hi.glide hv.hv hv.hQ z hz) ((show Continuous (fun M: Matrix (Tubular f G) (Tubular f G) ℝ=>glide M z) by unfold glide; fun_prop).continuousAt.tendsto.comp hp)
omit h he hv [φ.NeBot] in
private theorem momentum (X:X₀×ℝ) (i k:Tubular f G) : ContDiffAt ℝ (↑j) (fun y:X₀×ℝ=> glide (Matrix.of y.1) y.2 i k) X:=by simp_rw [glide, Matrix.add_apply,Matrix.smul_apply,Matrix.sub_apply, Matrix.of_apply]; fun_prop
lemma thought (M:Window (along (G:=G) S) n)(i :Ledger f 3): Frill φ j p (fun n y=> ArmA M (U n y) i) (fun n y=> ArmA M (U' n y) i):=by
   refine (Frill.stocks fun i=> Frill.stocks fun j=> h i j).fares (Q:=fun x:X₀=>ArmA M (Matrix.of x) i) (fun g hg=> sculpture _ _ (fun x y=> aSeq M (Matrix.of x) y) ?_); intro y hy k i l
   let A(X:X₀×ℝ):= glide (Matrix.of X.1) X.2; let Z:=(g,y); have hc p q: ContDiffAt ℝ (↑j) (fun z=> M.pad (A z) p q) Z := padP M _ (momentum Z) (shapes h he hv hg y hy) p q
   match k with
   | 0=> change ContDiffAt ℝ (↑j) (fun x:X₀×ℝ=> x.1 i l-_) _; fun_prop -- fix
   | 1 => exact hc i l
   | n+2=> exact ((ContDiffAt.sub (liftP A (momentum _) (fun x=> M.pad (A x)) hc i l) contDiffAt_const)).neg
lemma sphinx (M:Window (along (G:=G) S) n)(i : Ledger f 1): Frill φ j p (fun n y=> ArmS M (U n y) i) (fun n y=> ArmS M (U' n y) i):=by
   refine (Frill.stocks fun i=>Frill.stocks fun j=> h i j).fares (Q:=fun x:X₀=>ArmS M (Matrix.of x) i) (fun g hg=> sculpture _ _ (fun x y=> sSeq M (Matrix.of x) y) ?_)
   intro y hy k p q; let A(x:X₀×ℝ):=Matrix.of x.1
   have hA i k:ContDiffAt ℝ (↑j) (fun z=> A z i k) (g,y):=by change ContDiffAt _ _ (fun z:X₀×ℝ=>z.1 i k) _; fun_prop
   have hc i k:=padP M A hA (Buds.assured he (K:=Matrix.of g) hg) i k
   have hh i: ContDiffAt ℝ j (fun x=>M.frameMean (A x) i q) (g,y):=(hc i q|>.add (hc q i)).const_smul ((1:ℝ)/2)
   have hh' : ContDiffAt ℝ j (fun x=>M.flawed (A x) p q) (g,y):=(Vine.per_entry _ _ _ _ _ (hA p) hh).sub contDiffAt_const
   cases k; · exact hh'
   exact (contDiffAt_snd.smul hh').neg
lemma planets (M:Window (along (G:=G) S) n) (b:Bond f) : Frill φ j p (fun n y=> Batch.joint (U n y) M b) (fun n y=> Batch.joint (U' n y) M b):=by
   refine (Frill.stocks fun i=> Frill.stocks fun j=> h i j).fares (Q:=fun x:X₀=>Batch.joint (Matrix.of x) M b) ?_
   intro g hg; unfold Batch.joint; refine ContDiffAt.sum (fun i _=>?_); unfold localBase lact
   let f(x:X₀)(y:ℝ):= intensity M (Matrix.of x) y 0 (b,i) (b,i)
   simp_rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)]
   refine (Blaze.yoga (U:=f) ?_ |>.calls).1; intro y hy; let z:=(g,y); let U(x:X₀×ℝ):= glide (Matrix.of x.1) x.2
   have hc p k: ContDiffAt ℝ (↑j) (fun z=> M.pad (U z) p k) z := padP _ _ (momentum z) (shapes h he hv hg y hy) p k
   unfold f uncurry intensity; simp_rw [pow_zero,mul_one]; apply liftP _ _ _ hc; intro k l; simp_rw [Matrix.sub_apply,of_apply]; exact ContDiffAt.sub (by fun_prop) contDiffAt_const
end YM.ConnectedActivityE6.Lim
