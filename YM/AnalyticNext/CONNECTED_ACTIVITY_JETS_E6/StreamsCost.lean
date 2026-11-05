import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Cascades
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Castro

/-!
# Buying actual Arms across all normalized spectra, at marked derivative jets

Outputs per-label prices accurate before their fractions signs. Keep true
caps on both when comparing, not rebranching output tests. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Pulse Itinerary
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
open Brush Foramen  Gate  Vine Tablet Metric
variable {v z r Q s y η γ : ℝ} {j m n d B : ℕ} {x : E}
namespace Vine

def blurs (s : ℝ) (C : ℝ) (d k : ℕ) := C*(1+((1+d)*s))^k

def alert (S : StepData c f) (B j k : ℕ) (s c v : ℝ) (p : Ledger f k) :=
    cap S B k p (blurs s c k j) (v*(2:ℝ)^j)
lemma fluid (S : StepData c f) {B d : ℕ} (l : Ledger f d) {F : E→ℝ} (hv : 0≤v) (p : Brush j (cap S B d l z r)
    ((↑(l.1+d:ℕ):ℝ)*v) F x) : Brush j (alert S B j d v z r l) 1 F x := by
  apply p.trim.climb _ le_rfl; unfold alert cap
  by_cases h : Armed S (3*B) l.snd.1 l.snd.2
  swap; · rw [if_neg h,if_neg h,zero_mul]
  have hp:=p.nonneg; rw [cap,if_pos h] at hp
  rw [if_pos h,if_pos h]
  have he (i : ℕ) : i+1 ≤ (2:ℝ)^i := by
    induction i with
    | zero=> simp
    | succ i ih => rw [pow_succ]; push_cast; linarith [Nat.cast_nonneg (α:=ℝ) i]
  have hh : 0 ≤ z*r^l.1 := hp
  have hq : 1+(↑(l.1+d:ℕ):ℝ)*v ≤ (1+((1+d)*v))*2^l.1 := by
    have hg := he l.1; push_cast
    have hx : (↑(l.1):ℝ)+d ≤ (1+(d:ℝ))*(2:ℝ)^l.1 := by nlinarith [Nat.cast_nonneg (α:=ℝ) l.1,Nat.cast_nonneg (α:=ℝ) d]
    linarith [mul_le_mul_of_nonneg_right hx hv,Nat.cast_nonneg (α:=ℝ) l.1]
  apply (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hq j) hh).trans_eq
  unfold blurs; rw [mul_pow,mul_pow, ← pow_mul, ← pow_mul]; ring

lemma enlighten (P : Teller G) (L : Side) (D : Patch) (hd : D.Branches P.bind G) (l j : ℕ) (hl : 4≤l) {η r Q : ℝ} (ho : Torch η r Q) (t a ε : ℝ)
    (ht : t<0) (he : 0 ≤ a) {v : ℝ→ℝ} (h : Rate G L (-(1/2)) v) :
    ∃ B : ℝ → ℝ, Rate G L t B ∧ ∀ᶠ x in atTop, ∀ (c f : Side) (S : StepData c f) (T : Tube G S),
    S.patch=D → Works P L x S T → ∃ (Z : Ledger f 3→ℝ) (Y : Ledger f 1→ℝ),
      Sales (radiusB x) a ε (receipt S (radiusB x) l 3) Z Sigma.fst (B x) ∧
      Sales (radiusB x) a ε (receipt S (radiusB x) l 1) Y Sigma.fst (B x) ∧
      ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (F : Forest S.ratio) (X : Coat T F)
      (U : E→Config G c) (z:E), X.x=x→ Mode U z j (v x) → Allow (vary X (U z)).plate (along S) (tubularPrice G L) η r Q →
      (∀ i, Brush j (Z i) 1 (fun y=>ArmA X.shutter (vary X (U y)).plate i) z) ∧
      ∀ i, Brush j (Y i) 1 (fun y=>ArmS X.shutter (vary X (U y)).plate i) z := by
  obtain ⟨C,hC,hK⟩:= bounded_stencils P D hd
  let p:= min (P.top.width/2) (retain η r Q); have hp : 0 < p := lt_min (half_pos P.top.width_pos) ho.prices
  have hz : p < P.top.width := (min_le_left ..).trans_lt (by linarith [P.top.width_pos])
  have hr : p≤ retain η r Q := min_le_right ..
  let n:ℝ:= Fintype.card G.ColorIndex
  let f := carat D P L p C; let A:= f*f+1; let m:= tubularPrice G L; let s:=payE η r Q m
  let F:=1+(A+1); let H x:=facePrice j (radiusB x) m F s; let T x:=tidal p F (H x) (radiusB x)
  let K x:= A*(token j A s *tidal p A (facePrice j (radiusB x) m A s) (radiusB x))
  let g x:=kernelGrowth (radiusB x) G (v x); let w x:=g x+g x; let y x:= w x+driftP j (w x)
  let u x:= w x+(driftP j (w x)+y x)
  let C₁ x:=n^4*((A+1)*(H x*T x)); let C₂ x:= n*T x; let H₁ x:= n^2*K x; let H₂ x:= n*K x
  have hh := (jet_growth G L h).weaken (b:=0) (by norm_num)
  have hW : Rate G L 0 (fun x=>driftP j (w x)) := (hh.add hh).mul_left _
  have hx := swims G L t (polynomial G L j m F s) hp F
  have hu : Rate G L t K := ((swims G L t (polynomial G L j m A s) hp A).mul_left _).mul_left _
  have he' (y : ℝ→ℝ) (g : ℝ→ℝ) (h : Rate G L 0 y) (hk : Rate G L t g) (i : ℕ) : Rate G L t (fun x=> blurs (y x) (g x) i j) := by
    simpa only [zero_mul,add_zero] using! hk.mul ((Rate.add (Rate.const 1) (Rate.mul_left h _)).pow j)
  obtain ⟨Z,hZ,hV⟩:= out P L l 3 a ε he hl ht _ _ (he' y C₁ ((hh.add hh).add hW) (by
    convert ((((polynomial G L j m F s).mul hx).mul_left (A+1)).mul_left (n^(4:ℕ))) using 1; ring) 3)
    ((hx.mul_left n).mul_right ((2:ℝ)^j))
  obtain ⟨Y,hY,hO⟩:= out P L l 1 a ε he hl ht _ _ (he' u H₁ ((hh.add hh).add (hW.add ((hh.add hh).add hW))) (hu.mul_left _) 1)
    ((hu.mul_left n).mul_right ((2:ℝ)^j))
  refine ⟨fun x=>|Z x|+|Y x|,(hZ.compare (v:=fun x=> |Z x|) (Eventually.of_forall (fun x=> (abs_abs _).le))).add
    (hY.compare (v:=fun x=>|Y x|) (Eventually.of_forall fun x=> (abs_abs _).le)),?_⟩
  filter_upwards [hV,hO,room G P L] with x hx hX hp' c f S T hS ht'
  by_cases H' : ∃ N:ℝ, 0 ≤ v x ∧ N=0 -- need nonneg V maybe no Mode. If no always, sales null.
  swap
  · refine ⟨fun _=>0,fun _=>0,?_,?_,fun E _ _ _ F X U z h hh=>?_⟩
    any_goals refine ⟨fun _=>le_rfl, fun i=>?_⟩; simp [Reserves.tariff, SumBudget, add_nonneg (abs_nonneg (Z x)) (abs_nonneg (Y x))]
    exact False.elim (H' ⟨_,hh.pos,rfl⟩)
  obtain ⟨_,hs,-⟩:= H'
  have hq := hp' _ _ S T ht'
  have hb : 0≤ A := add_nonneg (mul_self_nonneg _) zero_le_one
  have hy : 0≤ y x := by unfold y w g driftP kernelGrowth; have := royalty_ge G; positivity
  have hw : 0≤ u x := by unfold u w g driftP kernelGrowth; have := royalty_ge G; positivity
  have hn : 0≤n := by unfold n; positivity
  have ha : 0≤s := mul_nonneg (mul_nonneg (tsum_nonneg fun j=> by unfold rates0; positivity) (Nat.cast_nonneg _))
    (inv_nonneg.mpr ((lt_min zero_lt_one (half_pos ho.spans)).le))
  have hf : 0≤F := by unfold F; linarith
  have hF (C) (hc:0≤C) : 0 ≤ token j C s := by unfold token; positivity
  have he'' (u) (h:0≤u) : 0≤facePrice j (radiusB x) m u s := mul_nonneg (Nat.cast_nonneg _) (hF u h)
  have hT : 0≤ H x := he'' F hf
  -- T shadow
  have hlh : 0≤ tidal p F (H x) (radiusB x) := by unfold tidal; positivity
  have hN : 0≤K x := by
    dsimp only [K]; unfold tidal; have := hF A hb; have := he'' A hb; positivity
  refine ⟨alert S (radiusB x) j 3 (y x) (C₁ x) (C₂ x),alert S (radiusB x) j 1 (u x) (H₁ x) (H₂ x),
    Sales.raise (hx c f S T ht'.length_eq hq ?_ ?_) ((le_abs_self _).trans (le_add_of_nonneg_right (abs_nonneg _))),
    Sales.raise (hX c f S T ht'.length_eq hq ?_ ?_) ((le_abs_self _).trans (le_add_of_nonneg_left (abs_nonneg _))), ?_⟩
  · dsimp only [blurs,C₁]; positivity
  · positivity
  · dsimp only [blurs,H₁]; positivity
  · positivity
  intro E _ _ _ F X U z he hx H
  subst x
  let f u:= (vary X (U u)).plate
  have hh := plates X _ hS ht'.length_eq hq hx C hC (hK _ _ S T hS ht'.funds) hp.le hz
  have ht (x:E): Thin (along S) (along S) (f x) (X.B/2) := (vary X _).span hq
  have hg : 4 ≤ X.B := le_trans (by norm_num) hq.sight.1
  exact ⟨fun i=> fluid _ i hy (glacierA X.shutter f ht hh H ho hr hg i), fun i=> fluid _ i hw (glacierS X.shutter f ht hh H hr hg (fun x=>(vary X (U x)).balanced) i)⟩
end Vine
end YM.ConnectedActivityE6.Blaze
