import YM.Next.RANK.Distant
import YM.Next.RANK.Radian.Allowance
import YM.Next.RANK.Radian.Foul
import YM.Next.RANK.Radian.Indices


/-!
# Use Kpcu on actual matrix stamps

Fourier parent hypothesis uses a cover chart already chosen--it asks the
*frequency* estimates, not any statement about positional Fourier bounds on
observations. It can e.g. use a finite-chart adjustment to stay away from other
integer grid singularities rather than relying on analytic outside-cube at one
infinite strip. All steps still with same path. Need it uniformly up to this
order d and budget. Stationary/RRack needs to ensure this with L growth and in its
currency. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Radian
open MeasureTheory Measure Filter Maxwell Topology Analysis Asymptotics Set Real Metric Beamer Lattice Prayer VectorFourier Finset
open Atlas Normal Perch Wall CellsInt Function
open scoped ContDiff Topology BigOperators Classical NNReal ENNReal FourierTransform RealInnerProductSpace

variable {H : Gauge} {C : Schedule} {n : ℕ} {F : E4→ℂ}
local notation "ℑ" => Complex.I

theorem TK (T D : Degree H) (R : ℕ) {t : ℝ} (ht : 0 < t) : ∃ c : ℝ,0 ≤ c ∧ ∀ F : E4→ℂ,∀ A : ℝ,1≤A→
    Integrable F → Mist (F-HeatP t T D) (T.degree+D.degree) A→Lip F R A→∀ (p : Side) (z : E4), 1 ≤ ‖z‖ →
      ‖(scansP p (fun x=>wave z x*F x) R).re-Prayer.gleam T D z‖ ≤ c*A*Wall.stature (T.degree+D.degree) z (p.val:ℝ):= by
  let d:=T.degree+D.degree
  obtain ⟨a,hA,ha⟩:=powder R
  let P:= HeatP t T D; let n:=d+5
  obtain ⟨b,hB,hb⟩:=indigo d
  obtain ⟨M,hv,hV⟩:= heat_perturbed T D ht n
  refine ⟨a+b+M,by positivity,fun F A h₁ h H hy p z hz=>?_⟩
  let v:= scansP p (fun x=>wave z x*F x) R;let x:= Prayer.gleam T D z
  have hu : Integrable P:= (Moment.assemble T D _ (fun _ _=> Moment.pressed _ (passion ht))).integral
  have he:‖harmon F z-harmon P z‖ ≤ A*b/‖z‖^n:= by
    have hc:harmon (F-P)=harmon F-harmon P:=harmon_sub h hu
    rw [← show harmon (F-P) z=harmon F z-harmon P z from congr_fun hc z]; exact hb _ _ H (zero_le_one.trans h₁) (h.sub hu) z hz
  have hh:= ha F A (zero_le_one.trans h₁) h hy p z
  change ‖harmon F z - v‖ ≤ _ at hh
  rw [norm_sub_rev] at hh
  apply le_trans (b:=‖v-(x:ℂ)‖);exact Complex.abs_re_le_norm (v-(x:ℂ)); refine le_trans (b:= ‖v-harmon F z‖ + (‖harmon F z - harmon P z‖+ ‖harmon P z-(x:ℂ)‖)) ?_ ?_
  · rw [show v-(x:ℂ)=v-harmon F z + (harmon F z- harmon P z+(harmon P z-(x:ℂ))) by abel]; exact (norm_add_le ..).trans (add_le_add_right (norm_add_le ..) _)
  apply (add_le_add hh (add_le_add he (hV z hz))).trans
  change _≤ _*Wall.stature d _ _; unfold Wall.stature; let p:ℝ:=(p.val:ℝ);let L:=(1+‖z‖)/p
  have hZ:0 ≤ L:= div_nonneg (by positivity) (by positivity); let X:=1 / ‖z‖^(d+5); have hX:0≤X:=by unfold X; positivity
  have hc : M*X≤ M*A*X:= mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hv h₁) hX
  calc
    _ = a*A*L + (A*b*X+M*X):= by unfold L X p n;ring
    _ ≤ (a+b+M)*A*(X+L):= by nlinarith only [hc,(show 0 ≤ a*A*X by positivity),(show 0 ≤ b*A*L by positivity),(show 0 ≤ M*A*L by positivity)]

lemma wave_add (x y z : E4) : wave (x+y) z=wave x z*wave y z:= by unfold wave; simp [inner_add_right,AddChar.map_add_eq_mul]

def stepsP (g : E4→ℂ) (p : Side) (R : ℕ) : E4 →ℂ := fun z=> scansP p (fun x=>wave z x*g x) R

def quant (e : E4) (g : E4→ℂ) (x : E4):= (wave e x-1)*g x
lemma instant (g : E4→ℂ) (p : Side) (R : ℕ) (z v : E4) : stepsP g p R (z+v)-stepsP g p R z=stepsP (quant v g) p R z:= by
  unfold stepsP scansP; rw [←smul_sub,← Finset.sum_sub_distrib]; apply congr_arg; apply sum_congr rfl; intro i _; dsimp only;rw [wave_add]; unfold quant;ring

def fling (n : ℕ) (t : Fin n → E4) (F : E4→ℂ) (x : E4) := (∏ i,(wave (t i) x-1))*F x
lemma orbital (g : Cover → E4) (f : Axis→E4) (hr : ∀ x i,g (x+step i)=g x + f i) (x : Cover) (p R) (T : Fin n→Axis) (F : E4→ℂ) :
    jumps n T (fun i=>(stepsP F p R (g i)).re) x= (stepsP (fling n (f∘ T) F) p R (g x)).re:= by
  induction n generalizing F with
  | zero=> rw [show fling 0 _ F=F by ext1;simp [fling]]; rfl
  | succ n ih=>
    let H:=quant (f (T 0)) F; let G:=f ∘ Fin.tail T
    have he : stepValue (fun i=>(stepsP F p R (g i)).re) (T 0)= (fun i:Cover=>(stepsP H p R (g i)).re):= by
      ext1 i; rw [stepValue,hr]; exact congr_arg Complex.re (instant ..)
    rw [jumps,he,ih];rw [show fling (n+1) (f∘ T) F=fling n (f∘ Fin.tail T) H by
      ext1 u; unfold fling H quant; rw [Fin.prod_univ_succ]; simp only [Function.comp_apply,  Fin.tail_def]; ring]

def captured (u v x y : Cover) := mapZ (u+x-(v+y))
def parade (a b : Degree H) (F : E4→ℂ):=fling a.degree (YM.basis ∘ a.layout) (fling b.degree ((-YM.basis) ∘ b.layout) F)
lemma seats (u v : Cover) (a b : Degree H) (p : Side) (R : ℕ) (F : E4→ℂ) (X : Bridge H)
    (h : ∀ x y,X (x,a.a,a.paint) (y,b.a,b.paint)=(stepsP F p R (captured u v x y)).re) : mourn (gesture a) (gesture b) X=(stepsP (parade a b F) p R (captured u v a.point b.point)).re := by
  change jumps _ _ (fun z=> jumps _ _ (fun i=> X _ _) _) _ = _
  simp_rw [h]
  let P:= fling b.degree ((-YM.basis)∘b.layout) F
  have he (i : Cover): jumps b.degree b.layout (fun z=>(stepsP F p R (captured u v i z)).re) b.point=(stepsP P p R (captured u v i b.point)).re:= orbital (captured u v i) (-basis) (fun x a=>by unfold captured;simp only [Wall.sends_sub,← add_assoc,mapZ_step,Pi.neg_apply]; abel) _ _ _ _ F
  simp_rw [he]
  let v':=fun i=>captured u v i b.point
  exact orbital v' basis (fun i j=>by unfold v' captured;simp only [Wall.sends_sub,← add_assoc,mapZ_step]; abel) _ _ _ _ _

-- stamp certificate from missing stationary and window costs. R global radius in
-- FREQUENCY (allow reps overlaps already accounted). jointly on Scale.Point.(P). No assertion
-- about rotation outside the stamp in this API.
structure Turbo (k p R n : ℕ) (L : AtlasData H C p) (b t : ℝ) : Prop where
  shutters u v : (∀ i, shutter (looked (L.κ k) u v i)) ∧ (∀ j,shutter (fun z=>looked (L.κ k) u v z j))
  valves (a c : Degree H) (ha : a.degree≤ n-1) (hc : c.degree≤ n-1): ∃ F : E4→ℂ,
    (∀ u v x y :Cover, (L.κ k).cov (body u (x,a.a,a.paint)) (body v (y,c.a,c.paint)) = stepsP F (C.side k p) R (captured u v x y)) ∧
    Integrable (parade a c F) ∧ Mist (parade a c F - HeatP t a c) (a.degree+c.degree) b ∧ Lip (parade a c F) R b

lemma commuting (Q : RG.Levels H) (h : H.Simple) (d R : ℕ) {t : ℝ} (ht : 0 < t): ∀ᶠ k in atTop,∀ p X, Turbo k p R d X (Perch.bill (1/2) (clim Q k)) t → Wall.Model Q d k p X:= by
  have hp: ∀ᶠ k in atTop, ∀ (a b : Hub H (d+2) 0), ∀ F : E4→ℂ,
      let C:= Perch.bill (1/2) (clim Q k)
      let n:= a.val.degree+b.val.degree
      Integrable F → Mist (F-HeatP t a.val b.val) n C → Lip F R C→∀ c z, 1 ≤ ‖z‖ →
        ‖(scansP c (fun x=>wave z x*F x) R).re- Prayer.gleam a.val b.val z‖ ≤ Perch.bill 1 (clim Q k)*Wall.stature n z (c.val:ℝ) := by
    refine eventually_all.mpr fun a=>eventually_all.mpr fun b=>?_ ; obtain ⟨c,hc,hQ⟩:=TK a.val b.val R ht
    filter_upwards [(Station.hat_rate Q h).eventually (Glimmer.transports (show (1/2:ℝ)<1 by norm_num) c)] with k hz F C n hu he hl c z hj
    apply le_trans (hQ F C (Glimmer.costed _ _ (by norm_num)) hu he hl _ _ hj); exact mul_le_mul_of_nonneg_right hz (by unfold Wall.stature; positivity)
  refine hp.mono fun k hv p X h=> ?_; refine ⟨h.shutters,fun u v a b ha hb hf=> ?_⟩
  obtain ⟨F,Hq,hm,hM,hw⟩:=h.valves a b ha hb
  let U (z : Degree H) (h : z.degree ≤ d-1) : Hub H (d+2) 0 := ⟨{z with point:=0},rfl,Nat.zero_le _,by dsimp;omega⟩
  rw [seats u v a b (Q.S.side k p) R F (looked (X.κ k) u v) (fun x y=> congr_arg Complex.re (Hq u v x y))]
  exact hv (U a ha) (U b hb) _ hm hM hw _ _ hf
end YM.Next.Rank.Radian
