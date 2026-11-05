import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Courants

/-!
# Crude Hardy and Bar. Before expenditure one actual θ

 Works with arbitrary held U even if all parents profitable; moment
 on allocated coherencies gains exponential reserves later.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine  Frond Corona Brush Foramen Gate Tablet Strokes Quill
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {k : Finset ℕ} {R : Rep G f} {X : Coat T F} {z : Air f G} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {x : E}
variable {a A α β γ d η σ W s b μ r Q p q v : ℝ} {j n : ℕ}
variable {V : E→ Config G c} {w : E → Directions G f} {u : E→ Air f G}

private lemma earnest (p : Works P L s S T) (U : Config G f) (q : S.Choices) (hV : Mode V x j 1) (i : Cell f) (ht : Pressure.fiery G s L ≤ 1) :
    let z:= royalty G; let A:=P.top; let F:= (A.paths*z^2)^2/2+(A.clip.direct*2+A.clip.linear*2)
    let M:=till s; let w:=shadowL P; let a := maxima P L M
    let t:= hikeZ G 1 M (dimLift P M 1)
    Brush j (F+2*(a*a+a*w)) (t+t) (fun z=> Scroll.loft T s U q (V z) false (.inl i)) x := by
  intro z A F M w a t
  let f:E→ Config G _:= fun _=>U
  let Q (v:E):= S.prediction U q
  have hp : P.Funds S T := p.funds
  have hJ : Primary P f V Q x w (dimLift P M 1) M T j := measures hp hV
    ⟨by norm_num,fun i=> a_oneB G (U i) zero_le_one⟩ ⟨by norm_num,fun i=>a_oneB G (S.prediction U q i) zero_le_one⟩ M
  have hM:= enCanvas hp hJ hV p.length_eq
  have hp (k : Bool) := hM.p0 (i,k); have hv:= (hp true).pos
  obtain ⟨b,C,h,-⟩:=p.funds.feeds
  have hE : ‖crown T.up T.high M 1 (Pressure.fiery G s S.patch.L) U i‖ ≤ F := by
    rw [p.funds.high,p.length_eq]; exact genuine T.up i U (temp_nonneg _) ht h (by decide)
  change Brush _ _ _ (fun z=> crown ..+∑ y:Bool, _) _
  have ht' : 0 ≤ t := hv
  refine ((Brush.certified (add_nonneg ht' ht') _).climb hE le_rfl).gathering ?_
  have he k := (semi (squared (hp k))).separating (stroke (hp k) ((hJ.high (i,k)).climb le_rfl (by
    unfold hikeZ; have hh:= royalty_ge G; apply le_add_of_nonneg_left; positivity)))
  apply (Brush.spree (univ (α:=Bool)) _ _ (by exact (he true).pos) (fun i _=> he i)).climb ?_ le_rfl; simp [w,a,maxima,mul_add]

lemma hearthLift (P : Teller G) (L : Side) (j : ℕ) {v : ℝ → ℝ} (h : Rate G L (-(1/2)) v) :
    ∃ C, Rate G L 0 C ∧ ∀ᶠ x in atTop, ∀ (c f:Side) (S : StepData c f) (T : Tube G S), Works P L x S T→
    ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (U : Config G f) (k : S.Choices) (V:E→ Config G c) (y:E),
      Mode V y j (v x) → ∀ v, Brush j (C x) 1 (fun i=> Scroll.loft T x U k (V i) false v) y := by
  let A:=P.top; let F:= (A.paths*royalty G^2)^2/2+(A.clip.direct*2+A.clip.linear*2)
  let M x:=till x; let w:=shadowL P; let a x:=maxima P L (M x)
  let t x:=hikeZ G 1 (M x) (dimLift P (M x) 1); let f x:= (F+2*(a x*a x+a x*w))*(1+(t x+t x))^j
  let g x:= scaleQ P L (M x)*(1+feeQ P (M x) 1)^j
  have hM := raking P L 1; have hh := Rate.const (G:=G) (L:=L) (1:ℝ)
  have hf (V : ℝ→ℝ) (h : Rate G L 0 V): Rate G L 0 (fun x=>(1+V x)^j) := by simpa only [zero_mul] using!
    ((hh.add h).pow j)
  have ht : Rate G L 0 a := (rateOfs P L (fun _=> w) (Rate.const _)).1
  have hF:Rate G L 0 f := by
    simpa only [zero_add] using! (((Rate.const F).add ((ht.mul ht|>.weaken (b:=0) (by norm_num)|>.add (ht.mul_right w)).mul_left 2)).mul
      (hf _ (hM.add hM)))
  have hG: Rate G L 0 g := by simpa only [zero_add] using! ((scaleRate P L).mul (hf _ (rateOfs P L (fun _=>1) hh).2))
  refine ⟨fun x=> |f x| + |g x|,(hF.compare (v:=fun x=> |f x|) (Eventually.of_forall fun x=> (abs_abs _).le)).add
    (hG.compare (v:=fun x=>|g x|) (Eventually.of_forall fun x=> (abs_abs _).le)),?_⟩
  filter_upwards [h.below (by norm_num) 1 zero_lt_one, (Rate.flame (G:=G) (L:=L)).below (by norm_num) 1 zero_lt_one] with
    x hx hv c f S T h E _ _ U k V y hp v
  have hV : Mode V y j 1 := ⟨zero_le_one,fun i=> (hp.atLink i).climb le_rfl ((le_abs_self _).trans hx)⟩
  rcases v with v|v
  · exact (earnest h U k hV v ((le_abs_self _).trans hv)).trim.climb ((le_abs_self _).trans (le_add_of_nonneg_right (abs_nonneg _))) le_rfl
  exact ((wild (k:=j) h.funds h.length_eq (U:=fun _=> U) ⟨by norm_num,fun i=> a_oneB G (U i) zero_le_one⟩ hV k
    ⟨by norm_num,fun i=> a_oneB G (S.prediction U k i) zero_le_one⟩ (.inr v) x).trim).climb ((le_abs_self _).trans
    (le_add_of_nonneg_left (abs_nonneg _))) le_rfl

-- Apply form⊥ to local data, without summing term budget repeatedly. Need pay color scale for lifting back to rod measure.
lemma balances (p : Room P S T X.x) (i : Mention c f) (x : Directions G f) : bar X x i=bar X 0 i + Coat.scale • X.motion x i := by
  unfold Vine.bar Coat.motion
  split
  next hh=>
    obtain ⟨u,V,h,-⟩:=p.accepted.feeds
    obtain ⟨L,hL⟩:=SliceRows.linear T X.R h i.1 i.2 X.V; unfold strain signal; rw [X.lens_zero,add_zero,← hL,← hL,← hL,map_add,← add_assoc,smul_add]
  simp

lemma foe (p' : Room P S T X.x) (i : Mention c f) (hV : Tablet j η q v (fun x=> (vary X (V x)).form) (aim S) (along S) x)
    (hp : ∀ b:G.ColorIndex, Brush j d v (fun x=> stand (bar (vary X (V x)) 0) (i,b)) x) (hp' : 0 ≤ d)
    (hu : ∀ i': Bond f, distAt S i' (root S i) ≤ X.B → X.Hot i'→ Brush j s v (fun k=> w k i') x) (hs : 0≤s) :
    Brush j ((Fintype.card G.ColorIndex:ℝ)*(d+q*s)) (v+v) (fun y=> bar (vary X (V y)) (w y) i) x := by
  let Z k:= vary X (V k)
  let U (x:E) (p:Bond f) := if X.Hot p ∧ distAt S p (root S i)≤ X.B then w x p else 0
  have he p : Brush j s v (fun x=> U x p) x := by
    unfold U; split_ifs
    next hp => exact hu _ hp.2 hp.1
    next => exact (Brush.certified hV.pos _).climb (by rw [norm_zero]; exact hs) le_rfl
  have hh : ∀ p : G.ColorIndex, Brush j (q*s) (v+v) (fun x'=> (Coat.scale • (Z x').motion (w x') i) p) x := by
    intro p
    refine (beam_vec (u:=fun x' => stand (U x')) hV hs hV.pos (fun j=> colorEvaluated j.2 (he j.1)) (i,p)).shimmy ?_
    refine Eventually.of_forall fun k=>?_
    obtain ⟨u,v,h,-⟩:= p'.accepted.feeds; have hp:= Z k|>.charged_for h (w k) (i,p)
    apply hp.trans; apply sum_congr rfl; intro j _
    let D:= (Z k).form (i,p) j
    change D*stand (w k) j=D*stand (U k) j
    by_cases he:X.Hot j.1
    · by_cases ht: distAt S j.1 (root S i)≤ X.B
      · unfold stand U; rw [if_pos ⟨he,ht⟩]
      unfold D; rw [(Z k).plume p' (i,p) j (by change X.B/4 < distAt S j.1 (root S i); omega),zero_mul,zero_mul]
    unfold D; rw [(Z k).stays _ j he p'.accepted,zero_mul,zero_mul]
  refine Blaze.tie G _ (add_nonneg hp' (mul_nonneg hV.basis hs)) (add_nonneg hV.pos hV.pos) ?_
  intro b; have hx := hp b; refine (((hx.climb le_rfl (le_add_of_nonneg_right hV.pos)).gathering (hh b))).shimmy ?_; exact
    Eventually.of_forall fun x=> by dsimp only; rw [balances (X:=vary X (V x)) p' i]; rfl
end YM.ConnectedActivityE6.Blaze
