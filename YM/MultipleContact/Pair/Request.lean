import YM.MultipleContact.Pair.Move

/-! Finite target geometries; punctured-domain estimates with a common positive radius. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.MultipleContact.Two
open Function Set Filter MeasureTheory Metric Table Power Direct
open scoped Topology BigOperators ContDiff Filter Classical
variable {G:Gauge}{L:Register G}{S:Table L}
section BasicRequest
variable {ι:Type*}[Finite ι]
structure Profile (L:Register G) where
  e:Exterior L
  support:Set (Points e.n)

def paint (e:Exterior L)(x:E4)(z:Points e.n)(h:Safe 0 z):Exterior L:=⟨e.n,Points.cons x (Points.across x z),e.letter, by
                 have he: Points.cons x (Points.across x z)=Points.across x (Points.cons 0 z):=by ext1 i; exact Fin.cases (zero_add x).symm (fun _=>rfl) i
                 rw [he]; exact Points.across_in _ h⟩
omit [Finite ι] in
lemma paint_self (e:Exterior L)(x:E4)(z:Points e.n)(h:Safe 0 z):relative (paint e x z h)=z:=by ext1 i;simp [paint,relative,Points.across_coord,Points.tail,Points.cons];change _ +x + -x=z.ofLp i;abel
omit [Finite ι] in
lemma translated_self (e:Exterior L):paint e (e.point 0) (relative e) (relative_safe e)=e:=by cases e with
 | mk n x q h=>
       suffices he:Points.cons (x 0) (Points.across (x 0) (relative (⟨n,x,q,h⟩:Exterior L)))=x by unfold paint; exact congr_arg' he
       ext1 i;refine Fin.cases rfl (fun j=>by simp [Points.cons,Points.tail,relative,Points.across_coord]) i
where
 congr_arg' {n:ℕ}{x y:Points (n+1)}{q:Fin n→L.Token}{hx:x∈conf (n+1)}{hy:y∈conf (n+1)}(eq:x=y):(⟨n,x,q,hx⟩:Exterior L)=⟨n,y,q,hy⟩:=by subst y; rfl

def Profile.covers (u:Profile L)(e:Exterior L):Prop := ∃ z∈u.support, ∃ hx:Safe 0 z, paint u.e (e.point 0) z hx=e

def targets (S:Table L) (u:ι→Profile L):Set (Target L):={t | t.fst=S ∧ ∃i, (u i).covers t.snd}
structure Eligible (u:ι→Profile L) : Prop where
  compact (i:ι) : IsCompact (u i).support
  room (i:ι) : Room (u i).support

variable (D:∀ k,Detector S k)
abbrev CoreIndices (N:ℕ):= (k:Fin (N+1)) × (D k.val).probes
def coreQ (N:ℕ)(i:CoreIndices (S:=S) D N):Profile L:=⟨i.2,{relative (i.2:Exterior L)}⟩
def includeIndexes {α:Type*} (N:ℕ)(u:α→Profile L):α ⊕ (CoreIndices D N) →Profile L:=Sum.elim u (coreQ D N)
omit [Finite ι] in
lemma eligible_core (N:ℕ):Eligible (coreQ D N):=⟨fun i=>isCompact_singleton,fun i z hz=>(mem_singleton_iff.mp hz).symm ▸ relative_safe (i.2:Exterior L)⟩
omit [Finite ι] in
lemma eligible_total {α:Type*}(N:ℕ){u:α→Profile L}(he:Eligible u):Eligible (includeIndexes D N u):=by
  refine ⟨fun i=>?_,fun i=>?_⟩ <;> cases i with
  | inl i => first | exact he.compact i | exact he.room i
  | inr i => first | exact (eligible_core (S:=S) D N).compact i | exact (eligible_core (S:=S) D N).room i
omit [Finite ι] in
lemma active_total {α:Type*}(N:ℕ){u:α→Profile L}{k:ℕ}(h:k≤N)(e:(D k).probes):⟨S,e.val⟩∈ targets S (includeIndexes D N u) := by
    let x:Fin (N+1):=⟨k,by omega⟩; refine ⟨rfl,Sum.inr ⟨x,e⟩,(relative e.val),Set.mem_singleton _,relative_safe e.val,?_⟩
    exact translated_self _

variable {D}
lemma Eligible.pick {u:ι→Profile L}(h:Eligible u) : ∃ r> (0:ℝ),∀y∈closedBall (0:E4) r, ∀i:ι,∀z∈(u i).support,y≠0→away y z∈conf _:=by
   choose s hs hrew using fun i=> Room.reach (h.room i) (h.compact i)
   have he:∀ᶠ x in 𝓝 (0:ℝ), ∀i, x<s i := eventually_all.mpr fun i=> Filter.mem_of_superset (Metric.ball_mem_nhds (0:ℝ) (hs i)) (by intro x hx;exact (abs_lt.mp (by simpa only [mem_ball,dist_zero_right,Real.norm_eq_abs] using hx)).2)
   obtain ⟨r,hL,hr⟩:= ((show ∀ᶠ x in 𝓝[>] (0:ℝ), x∈Ioi (0:ℝ) from self_mem_nhdsWithin).and (he.filter_mono nhdsWithin_le_nhds)).exists
   refine ⟨r,hL,fun y hY i z hz hy=>?_⟩
   have hf:‖half y‖<s i:=((half_norm y).trans (by simpa only [mem_closedBall,dist_zero_right] using hY)).trans_lt (hr _)
   apply away_clear hy <;> apply hrew i <;> first | assumption | simpa only [mem_ball,dist_zero_right,norm_neg] using hf

variable {n:ℕ}
omit [Finite ι] in
lemma continuous_value (T:Table L)(h:T.Smooth)(A B:S.Tag)(q:Fin n→L.Token){z:Points n}{y:E4}(hz:away y z∈conf _) : ContinuousAt (fun p:E4× Points n=>pairValue T A B q p.1 p.2) (y,z):=by
    have hw:Continuous (fun p:E4× Points n=>away p.1 p.2) := by
       have h₀:Continuous fun p:E4×Points n=>half p.1:=half_continuous.comp continuous_fst
       unfold away positions; exact (continuous_cons.comp ((continuous_fst.add h₀.neg).prodMk (continuous_cons.comp (h₀.neg.prodMk continuous_snd))))
    refine ((class_smooth' h S _ hz).continuousAt.comp_of_eq hw.continuousAt rfl) -- cannot extension notation from private where in open?
where
  class_smooth' {T:Table L}(h:T.Smooth)(S:Table L){n}(w:Fin n→S.Tag){x:Points n}(hx:x∈conf n):ContDiffAt ℝ ∞ (fun y=>S.useAt T y w) x:= (S.class_smooth T h w x hx).contDiffAt ((conf_open _).mem_nhds hx)
section Measurability
local notation "ρ" => (fun r:ℝ=> (volume.restrict (ball (0:E4) r)))
omit [Finite ι] in
private lemma image_kas {f:E4→ℂ}{a r:ℝ}(he:0<a)(hr:r<a)(ht:ContinuousOn f (closedBall 0 a \ ({0}:Set E4))): AEStronglyMeasurable f ((ρ) r):=by
   let R:= closedBall 0 a \ ({0}:Set E4)
   have h0:MeasurableSet R := MeasurableSet.diff isClosed_closedBall.measurableSet (measurableSet_singleton _)
   refine ((aestronglyMeasurable_indicator_iff (μ:=volume) h0).2 (ht.aestronglyMeasurable h0)).mono_measure (Measure.restrict_le_self (μ:=volume)) |>.congr (?_ : R.indicator f =ᶠ[ae ((ρ) r)] f)
   filter_upwards [ae_off (R:=r) (show 1 ≤ Module.finrank ℝ E4 by simp [E4]), ae_restrict_mem isOpen_ball.measurableSet] with y hy ht
   have hi: y∈ R := ⟨Metric.mem_closedBall.mpr ((le_of_lt (Metric.mem_ball.mp ht)).trans hr.le), fun h=>hy (by simpa only [Set.mem_singleton_iff] using h)⟩
   exact Set.indicator_of_mem hi f

lemma quota {u:ι→Profile L}(h:Eligible u){r:ℝ}(hr:0<r)(hf:∀y∈closedBall (0:E4) (2*r), ∀i:ι,∀z∈(u i).support,y≠0→away y z∈conf _){f:FamilyData ℂ L}{p:ℝ}(hw:AtPrice f p)
    (hq:∀i,ContinuousOn (fun y:E4 × Points (u i).e.n=> f (u i).e y.1 y.2) ((closedBall 0 (2*r) \ ({0}:Set E4)) ×ˢ (u i).support)):
    ∃c:ℝ,∀i,∀z∈(u i).support, Kas r p c (fun y=>f (u i).e y z):=by
    let r':=r*2
    have hc(i):ContinuousOn (fun y: Points (u i).e.n × E4=>f (u i).e y.2 y.1) ((u i).support ×ˢ (ball 0 (2*r) \ ({0}:Set E4))):=by
        let W : (Points (u i).e.n × E4)→E4×Points (u i).e.n := fun x => (x.2,x.1)
        change ContinuousOn ((fun y:E4 × Points (u i).e.n => f (u i).e y.1 y.2) ∘ W) _
        apply (hq i).comp (Continuous.continuousOn (by fun_prop : Continuous W))
        exact fun x hx=>Set.mem_prod.mpr ⟨⟨Metric.mem_closedBall.mpr (Metric.mem_ball.mp (Set.mem_prod.mp hx).2.1).le,(Set.mem_prod.mp hx).2.2⟩,(Set.mem_prod.mp hx).1⟩
    choose c hC hq' using fun i=>repair (h.compact i) _ (hw _ _ (h.compact i) (h.room i)) (2*r) (hc i) r (by linarith)
    obtain ⟨v,hv⟩:=Finite.bddAbove_range c
    have hh (i)(z)(hz:z∈(u i).support):AEStronglyMeasurable (fun y=>f (u i).e y z) ((ρ) r):=by
         apply image_kas (show (0:ℝ)<2*r by linarith) (show r<2*r by linarith)
         change ContinuousOn ((fun y : E4 × Points (u i).e.n => f (u i).e y.1 y.2) ∘ fun y:E4=>(y,z)) _
         apply (hq i).comp (Continuous.continuousOn (continuous_id.prodMk continuous_const : Continuous (fun y:E4=>(y,z))))
         exact fun y hy=>Set.mem_prod.mpr ⟨hy,hz⟩
    refine ⟨max 1 v,fun i z hz=>⟨lt_of_lt_of_le zero_lt_one (le_max_left ..),hh i z hz,fun y hy hy' =>?_⟩⟩
    exact (hq' i z hz _ (⟨Metric.mem_closedBall.mpr ((Metric.mem_ball.mp hy).le), fun h=>hy' (Set.mem_singleton_iff.mp h)⟩)).trans (mul_le_mul_of_nonneg_right ((hv (mem_range_self _)).trans (le_max_right ..)) (Real.rpow_nonneg (norm_nonneg y) p))
end Measurability
end BasicRequest
end YM.MultipleContact.Two
