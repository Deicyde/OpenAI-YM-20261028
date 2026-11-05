import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Tatami


/-!
# Weak costing in growing numerical hulls.

Keep `Primary` covenant and Canva in chart-change. Caller can weaken
with bigger brushes uniformly. Keep α variable because livelihoods with
large-period stencils and bright κ support. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze
open Filter Function Lattice RG Pressure Pressure.Tube Pressure.Stores Work.E03 Work.F03 Exterior Wilson Push Push.AbsoluteSums Finset
open Precision Shell Channel Next.Fluctuations Bloch Laurent SliceRows Mask Coat SliceRows.DataKernel Scroll Strokes Quill
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical InnerProductSpace
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S}
variable {s : ℝ} {P : Teller G} {L : Side} {o : Site c} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {k j : ℕ} {U : E→ Config G f} {V Q : E→ Config G c} {x : E} {v z a w b d e : ℝ}
open Brush

lemma rooft {A : Clip} (t : ℝ) (h : 0≤ t) (hp : t≤1) (v : G.El) :
    |PathData.clipped A t (G.chord v)| ≤ A.direct*2+A.linear*2 := by
  have hy := G.chord_le_two v; have hh := G.chord_nonneg v
  have hv := A.quadratic_pos; have hA := A.tail_pos
  unfold PathData.clipped; split <;> rw [abs_of_nonneg (by positivity)]
  · have hm := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hh hy 2) hv.le; linarith
  nlinarith only [mul_le_mul_of_nonneg_left (mul_le_mul hp hy hh zero_le_one) hA.le,hv]

lemma genuine {R M : ℕ} (Y : PathData G) (i : Cell c) {P : Clip} {C τ Λ : ℝ} (U : Config G c)
    (h : 0 ≤ a) (hh : a≤1) (he : Y.Bounds P τ C Λ) (hr : 0<M) :
    ‖crown Y P R M a U i‖ ≤ (C*royalty G^2)^2/2+(P.direct*2+P.linear*2) := by
  refine (norm_add_le _ _).trans (add_le_add ?_ (rooft a h hh _))
  have he' := (shortened Y i R M hr he (k:=0) (d:=0) le_rfl (U:=fun _:ℝ=>U) (x:=(0:ℝ))
    (fun j=> a_oneB G (U j) le_rfl)).bound
  unfold trunk; split
  · rw [Real.norm_of_nonneg (by positivity)]; gcongr
  rw [norm_zero]; positivity

-- gridded outputs. Keep Stage query exact fees, carry clipped RHS only when U const.

def maxima (P : Teller G) (L : Side) (B : ℕ) := payZ P L B (shadowL P)


def scaleQ (P : Teller G) (L : Side) (R : ℕ) :=
    let u := shadowL P; let Q:= maxima P L R
    ‖P.top.clip.direct‖*flawBill G +2*((u+Q)*(u+Q))+
    (‖P.bind.penalty‖*flawBill G +(u+Q)*(u+Q))+
    (‖P.below.clip.direct‖*flawBill G+(ldCost u Q+octaves u (payZ P L R Q))) + Q*Q

def feeQ (P : Teller G) (R : ℕ) (v : ℝ) :=
    let D:= hikeZ G v R (hikeZ G v R (dimLift P R v)); D+D

lemma wild (p : P.Funds S T) (hL : S.patch.L=L) (hU : Mode U x k v) (hV : Mode V x k v) (t : S.Choices)
    (hQ : Mode (fun i=> S.prediction (U i) t) x k v) (o : Spot c f) (s : ℝ) :
      Brush k (scaleQ P L (till s)) (feeQ P (till s) v) (fun i=> loft T s (U i) t (V i) true o) x := by
  let Q i:= S.prediction (U i) t; let R := till s; let m:= shadowL P; let w:=dimLift P R v
  let n:= maxima P L R; let B:= payZ P L R n; let d:=hikeZ G v R w; let e:=hikeZ G v R d
  have h : Primary P U V Q x m w R T k:= measures p hV hU hQ R
  have hM : Canopied U V Q R k T n d B e x := enCanvas p h hV hL
  have hs := royalty_ge G; have hf := hV.pos
  have hh : w ≤ d ∧ d≤e := by unfold e d hikeZ; constructor <;> linarith [show 0≤ 2*(R:ℝ)*v*royalty G by positivity]
  have hn : 0≤ n := (hM.p1 (0,0)).nonneg
  have ht : 0≤ B := by unfold B payZ typesL; positivity
  have he := hh.2
  have hr : d+d≤ e+e := add_le_add he he
  have hy : 4*(v*royalty G)≤w ∧ v*royalty G+v ≤ w := by
    have hp : 0 ≤ max 0 P.η := le_max_left ..
    have he : 0 ≤ 2*(R:ℝ)*(v*royalty G) := by positivity
    unfold w dimLift; rw [add_mul]
    constructor <;> nlinarith [show 0 ≤ v*royalty G by positivity]
  let H1 := ‖P.top.clip.direct‖*flawBill G +2*((m+n)*(m+n)); let H2:= ‖P.bind.penalty‖*flawBill G+(m+n)*(m+n)
  let H3 := ‖P.below.clip.direct‖*flawBill G+(ldCost m n+octaves m B)
  have hf : 0 ≤ flawBill G := by unfold flawBill; positivity
  have hu : 0≤m := h.cost
  have h1 : 0≤H1 := by unfold H1; positivity
  have h2 : 0≤H2 := by unfold H2; positivity
  have h3 : 0≤H3 := by unfold H3 ldCost octaves; positivity
  have h4 : 0≤n*n := by positivity
  change Brush k (H1+H2+H3+n*n) (e+e) _ x
  rcases o with i|i|i|i
  · apply (beautyF R h hM hh.1 i hU (hy.1.trans hh.1)).climb _ hr
    rw [p.high]; change H1≤_; linarith
  · apply (beautyI R h hM hh.1 i hV hQ (by exact hy.2.trans hh.1)).climb _ hr
    rw [p.knobs]; change H2≤_; linarith
  · have hv : Brush k (‖P.below.clip.direct‖*flawBill G) (e+e) (fun j=> stormC T (V j) i) x := by
      have hq : Brush k (royalty G) e (fun j=> G.mat (faceValue (V j) i)) x := by
        have hv:= tour (U:=V) (square i.2.val.1 i.2.val.2) i.1 hV.pos hV.atLink
        exact hv.climb le_rfl (by exact (hy.1.trans (hh.1.trans hh.2)))
      have hf := (cracked (f:=fun z=> faceValue (V z) i) hq).smul (-T.low.direct)
      apply hf.climb _ le_rfl; rw [norm_neg,p.low]
    apply (hv.gathering (((graceL R h hM hh.1 i).climb le_rfl hr).gathering (graceD R h hM hh.1 hh.2 i))).climb _ le_rfl
    change H3≤_; linarith
  · apply (semi (squared (hM.p2 i))).climb _ hr; linarith only [h1,h2,h3]

lemma frontier (_P : Teller G) (L : Side) : Rate G L 0 (fun x : ℝ => (Animals.ballCost (till x):ℝ)) := by
  apply (Census.width_rate G L 1 0).compare
  refine Eventually.of_forall fun x=> ?_; simp only [one_mul,add_zero,Animals.ballCost]; rw [abs_of_nonneg (Nat.cast_nonneg _),abs_of_nonneg (Nat.cast_nonneg _)]
  gcongr <;> exact Nat.div_le_self _ _
lemma rateOfs (P : Teller G) (L : Side) (u : ℝ→ℝ) (h : Rate G L 0 u) :
    Rate G L 0 (fun x=>payZ P L (till x) (u x)) ∧ Rate G L 0 (fun x=>feeQ P (till x) (u x)) := by
  have he : Rate G L 0 (fun x : ℝ => (till x:ℝ)) := by
    apply Rate.compare Rate.radius_price; refine Eventually.of_forall fun x=>?_ ; rw [abs_of_nonneg (Nat.cast_nonneg _),
      abs_of_nonneg (Nat.cast_nonneg _)]; gcongr; exact Nat.div_le_self _ _
  have hv := h.mul_right (royalty G)
  have hh : Rate G L 0 (fun x => 2*(till x:ℝ)*u x*royalty G) := by
    convert (((he.mul_left 2).mul h).mul_right _) using 1; ring
  refine ⟨?_,?_⟩
  · simpa only [add_zero] using! (((frontier P L).mul_right (coversMark L)).mul (h.mul_left (typesL P)))
  have hk : Rate G L 0 (fun x=> dimLift P (till x) (u x)) := by
    unfold dimLift
    apply Rate.add (Rate.add _ _) (Rate.const _)
    · simpa only [add_zero] using! (((Rate.const 4).add (he.mul_left 2)).mul hv)
    exact hv.add h
  exact (hh.add (hh.add hk)).add (hh.add (hh.add hk))
end YM.ConnectedActivityE6.Blaze
