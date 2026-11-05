import YM.MergeProof.Selection
import YM.MergeProof.TeamFlow
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Daisy.Kiln


set_option autoImplicit false
noncomputable section
namespace YM.Merge.Palette
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Contract Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse
open Coat Matter ProbabilityTheory Poll Pond PhysicalNext.Repeat PhysicalNext.Repeat.Lotus Greenbelt
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {ι : Type} [Fintype ι] {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}

variable (M:ι→Lotus.Leaf R)
abbrev sign (S:StepData c f)(i:ι):= (M i).turn.badge S
def team (p:Tickets (sign M S)):Lotus.Team R:= ⟨p.val.image M,by
  intro j hj k hk hp; obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hj; obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp hk; exact congr_arg M (p.prop hi ha (show sign M S i=sign M S a from congr_arg (·.badge S) hp))⟩
omit [Fintype ι] in
lemma label (p:Tickets (sign M S)) : (team M p).signs S=p.reach:=by unfold team Team.signs Tickets.reach; rw [Finset.image_image]; rfl
omit [Fintype ι] in
lemma localized (p:Tickets (sign M S))(V:Molecule S): (team M p).locate V=team M (p.select V):=by
  have h: ∀ (M N : Team R),M.own=N.own→M=N:=by rintro ⟨x,y⟩ ⟨t,w⟩ h; congr
  apply h; ext i; constructor
  · intro hi; obtain ⟨ht,hk⟩:=mem_filter.mp hi; obtain ⟨p,hp,rfl⟩:=mem_image.mp ht; exact mem_image_of_mem _ (mem_filter.mpr ⟨hp,hk⟩)
  intro hi; obtain ⟨j,hj,rfl⟩:=mem_image.mp hi; obtain ⟨ht,hk⟩:=mem_filter.mp hj; exact mem_filter.mpr ⟨mem_image_of_mem _ ht,hk⟩

variable (Y:Cash W x μ L Q o C T R) (χ:Chi) (U:Config G c)
-- Tips without weeds.P
def act (k: Molecule S)(p:Tickets (sign M S)):= let _:=Y; (team M p).lotus T x χ o.K W o.a Q.table Q.halo U k -- unused Y put
local notation "w'"=> sign M S
omit [Fintype ι] in
lemma present (p:Tickets (sign M S))(k: Molecule S)(hn:act M Y χ U k p≠0): p.reach⊆k∧ standsIn (planted (prism T x χ o.K U F) k) R Q.halo k:=by -- second maybe false planted all flags. change
  let B:=(team M p); let Z r:=B.bloom (prism T x χ o.K U (allot r)) W o.a Q.table Q.halo k
  obtain ⟨r,h⟩:∃ i,Z i≠0:=by by_contra! h; apply hn; change _ *∑ i,Z i=0; rw [Finset.sum_eq_zero (fun i _=>h i),mul_zero]
  have ht:p.reach ⊆ k:=by rw [← label]; exact Classical.byContradiction (fun hx=>h (B.bloom_off _ k hx))
  exact ⟨ht,(by by_contra hn; exact h (if_neg (show ¬standsIn _ _ _ _ from hn)))⟩
variable (v:ι→ℝ)
def color (k: Molecule S) :=∑ i:Tickets (w'),(∏ j∈i.val,v j)*act M Y χ U k i

def sale (R' : Tickets (w'))(u : Config G f):=(∏ j∈R'.val,v j)*(team M R').cicada u

def buy (S : StepData c f) (u:Config G f):=∑ i:Tickets (sign M S),sale M v i u

include Y
 -- include
lemma remit (A : Finset (Molecule S)) : Y.festo U (color M Y χ U v) A = ∑ p:Tickets (w'),(∏ j∈p.val,v j)*(team M p).blossom T x χ o.K W o.a Q.table Q.halo U A:=by
  letI : Nonempty (Forest S.ratio):= Tree.select S.ratio S.patch.odd_side
  let l:=A.biUnion id
  by_cases h : joints T R Q.halo (radiusB x) A ∧ permitsA x U A
  swap
  · rw [show Y.festo _ _ _=0 from if_neg h]; symm; exact sum_eq_zero fun i _=>by rw [Team.blossom, if_neg (fun hi=>h ⟨hi.1,hi.2.1⟩),mul_zero] -- edit
  let f p i:= act M Y χ U p i
  let g (p:Tickets (w')):=(∏ j∈p.val,v j)
  have hb(p : Molecule S) : color M Y χ U v p=∑ i:Tickets.Applies (w') p,g i.val*f p i.val:= Tickets.confined _ _ (fun i hi=> (present M Y χ U i p (F:= Classical.ofNonempty) (right_ne_zero_of_mul hi)).1)
  let m(i:Tickets (w')):=g i*(team M i).blossom T x χ o.K W o.a Q.table Q.halo U A
  have ht: (∑ i,m i)=∑ i:Tickets.Applies (w') l,m i.val:= Tickets.confined _ _ (fun a hi=> by
    rw [← label]; have hx:=right_ne_zero_of_mul hi; unfold Team.blossom at hx; split at hx;next h=>exact h.2.2
    next=>exact (hx rfl).elim)
  unfold Cash.festo; dsimp only; rw [if_pos h]; change _=∑ i,m i; rw [ht]; simp_rw [hb]; refine (Tickets.on_record (w:=w') A id (unweave h.1) f v).trans ?_
  refine sum_congr rfl fun p _=> ?_; unfold m g Team.blossom; rw [if_pos (show _∧_∧_ from ⟨h.1,h.2,label M p.val|>.symm ▸ p.prop⟩)]; simp_rw [localized]; rfl

lemma pushed (F:Forest S.ratio) : HasSum (fun p=> overhead (prism T x χ o.K U F) R Q.table * Y.festo U (color M Y χ U v) p) (S.push R.beta (buy M v S) U):=by
  let g (p:Tickets (w')):=(∏ i ∈ p.val,v i); let H (p:Tickets (w')) (W:Config G f):=(team M p).cicada W
  have h:=hasSum_sum (s:=univ) (fun i (_:i∈(univ:Finset (Tickets (w')))) => ((team M i).summons T x χ Y F U).mul_left (g i))
  have he : (∑ i,g i*S.push R.beta (H i) U)=S.push R.beta (buy M v S) U := by
    unfold StepData.push buy sale; simp_rw [← integral_const_mul, smul_eq_mul, Finset.mul_sum]
    have hK := S.isKernel (funds_branch Y.laws.intake.ready) R.beta -- signature?
    change _=∫ a, ∑ p:Tickets (sign M S), S.density R.beta a U • sale M v p a ∂prior G f
    rw [integral_finsetSum _ (fun p _=> StepData.push_slice hK U _ (show Integrable (sale M v p) (prior G _) from ((Envelope.const _ |>.mul ((team M p).sells Y.laws.intake.cap).1 : Envelope (sale M v p)).integrable _)))]
    apply Finset.sum_congr rfl; intro p _; apply integral_congr_ae; filter_upwards with X; exact show g p * (_ * H p X)= S.density R.beta X U*(g p * H p X) from mul_left_comm .. 
  rw [← he]; apply h.congr_fun
  intro i; rw [remit,Finset.mul_sum]; exact sum_congr rfl fun j _=> mul_left_comm ..
end YM.Merge.Palette
