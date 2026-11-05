import YM.MergeProof.Palette
import YM.MergeProof.Spread
import YM.MergeProof.SwitchCost
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Daisy.Solvent

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
variable (M:ι→Lotus.Leaf R)(Y:Cash W x μ L Q o C T R) (χ:Chi)
local notation "w"=> sign M S
local notation "sx"=> radiusB x
lemma likely_norm {α : Type}[Fintype α][Nonempty α] (p:α→ℝ) (a:ℝ)(ha:∀ i,‖p i‖ ≤ a): ‖likely p‖ ≤ a:=by
  unfold likely; rw [norm_mul,Real.norm_of_nonneg (by positivity : 0 ≤ ((Fintype.card α:ℝ)⁻¹))]; have h:=mul_le_mul_of_nonneg_left ((norm_sum_le ..).trans (sum_le_sum (s:=univ) fun i _=>ha i)) (by positivity : 0 ≤ ((Fintype.card α:ℝ)⁻¹)); simp only [sum_const,nsmul_eq_mul,card_univ] at h; exact h.trans_eq (inv_mul_cancel_left₀ (by positivity: (Fintype.card α:ℝ) ≠ 0) _)
omit [Fintype ι] in
lemma act_norm (p:Molecule S)(i:Tickets w)(U:Config G c)(h:i.reach ⊆ p) :
    ‖act M Y χ U p i‖≤ (team M i).weight*∏ j∈ p\i.reach,Y.text j:=by
  letI:Nonempty (Forest S.ratio):=Tree.select S.ratio S.patch.odd_side
  let M':=team M i; unfold act Team.lotus; refine likely_norm _ _ fun T0=>?_ ; unfold Team.bloom; split
  next hv=>
    unfold Team.steep; apply likely_norm; intro j; apply (norm_integral_le_integral_norm _).trans
    let V:=prism T x χ o.K U (allot T0)
    have he := M'.tip ((planted V p).taggedL j) (own p) Y rfl (planted_valid V p) p
    exact he.2.2.trans_eq (by rw [label M i,if_pos h]; congr!)
  rw [norm_zero]; exact mul_nonneg M'.profit (prod_nonneg fun i _=>Y.positive i)
omit [Fintype ι] in
lemma worth (p:Tickets w): (team M p).weight=∏ i∈p.val,(M i).weight:=by unfold Team.weight team; rw [Finset.prod_image]; exact fun _ hx _ hy h=>p.property hx hy (show sign M S _= _ from (by unfold sign; rw [h]))

open Switch
variable (rA:ι→ℝ) (hp:∀ i, 0≤ rA i)
def ways (x:ℝ) (v:Finset ι)(i:ι):= if i∈v then rA i*x else 0
omit [Fintype ι] in
lemma amplitudes (p: Finset ι)(x:ℝ)(v:Finset ι): ∏ i∈p, ways rA x v i = click p (∏ i∈p,rA i) x v:=by
  by_cases h:p⊆v
  · unfold click; rw [if_pos h, show ∏ i∈p,ways rA x v i=∏ i∈p,rA i*x from prod_congr rfl fun i hi=> if_pos (h hi),prod_mul_distrib,prod_const, mul_comm]
  rw [click,if_neg h]; obtain ⟨i,hi,hx⟩:=Finset.not_subset.mp h; exact prod_eq_zero hi (if_neg hx)
def wages (u:ι): ℝ:=rA u*(M u).weight

def toll (i:Head S): ℝ:= let _:=Y; Y.text i+Tickets.extra w (wages M rA) i

def vote (p : Molecule S) (U:Config G c)(x:ℝ)(v: Finset ι):=color M Y χ U (ways rA x v) p
include hp
lemma ad (p:Molecule S)(i:Tickets (sign M S)):
    Paid (fun U x v=> (∏ j∈i.val,ways rA x v j)*act M Y χ U p i) (if i.reach ⊆ p then (∏ j∈i.val,wages M rA j)*∏ j∈p\i.reach,Y.text j else 0):=by
  split
  next h=>
    let v:= ∏ j∈i.val,rA j; let z U:=v*act M Y χ U p i; have he : (∏ j∈i.val,wages M rA j)=v*(team M i).weight:=by rw [worth]; unfold wages; rw [prod_mul_distrib]
    have ht : 0≤ v:= prod_nonneg fun i _=> hp i
    rw [he,mul_assoc]; apply Paid.congr (paidClick (ι:=ι) i.val (p:=z) (mul_nonneg ht (mul_nonneg (Team.profit _) (prod_nonneg fun i _=>Y.positive i))) (fun j=> ?_))
    · intro u x hz; ext v; rw [amplitudes]; unfold click z; split_ifs <;> ring
    unfold z; rw [norm_mul, Real.norm_of_nonneg ht]; exact mul_le_mul_of_nonneg_left (act_norm M Y χ p i _ h) ht
  next h =>
    letI:Nonempty (Forest S.ratio):=Tree.select S.ratio S.patch.odd_side
    apply Paid.congr paidZero; intro u x hx; ext v; rw [show act M Y χ _ p i=0 from Classical.byContradiction (fun he=>h ((present M Y χ u i p (F:= Classical.ofNonempty) he).1)),mul_zero]; rfl
lemma payments (p : Molecule S) : Paid (vote M Y χ rA p) (∏ i ∈p,toll M Y rA i):= by
  rw [show (∏ i∈p,toll M Y rA i)= _ from Tickets.expanded w _ _ p] -- infer
  refine Paid.congr (Paid.sum univ _ _ (fun i _=> ad M Y χ rA hp p i)) ?_; intro u x hx; ext i; simp only [Finset.sum_apply]; rfl

open Mixed

-- cost to pay. same Africa budget.X Δ
local notation "X'"=> Daisy.swing Q L μ R.beta x C
def mark (i:ι):=Daisy.sparkling c f (M i).turn -- pulls c via value info?
def pitch (i:ConnectedActivityE6.Alphabet c f):= Y.opt i + Tickets.extra (mark M) (wages M rA) i
local notation "d"=> ConnectedActivityE6.lengths T R
local notation "kd"=> steamP S (Q.costs L μ R.beta x C)
def tune (n k:ℕ)(p:Molecule S):= selected S Q.halo sx X' Y.birth (pitch M Y rA) d kd 0 k n 0 p
lemma votes (p:Molecule S)(n k:ℕ)(hn:n≤Cash.numP p): Paid (vote M Y χ rA p) (tune M Y rA n k p):=by
  let f:=vote M Y χ rA p; let t:=X'
  by_cases h:Y.ticketsP 0 n 0 p
  · have hr : ∀ i,toll M Y rA i= Mixed.costs S Q.halo sx kd (pitch M Y rA) i := by
       intro i; rcases i with i|i
       · unfold toll Tickets.extra; rw [sum_eq_zero, add_zero]; · rfl
         intro j _; exact if_neg (fun h=> by have hf:=(show .inr _ = sign M S j from Daisy.sparkPath ..).trans h; contradiction)
       unfold toll Tickets.extra Cash.text Mixed.costs pitch Tickets.extra
       dsimp only [Sum.elim]; simp_rw [← show ∀ j, (.inr (mark M (c:=c) j):Head S)=sign M S j from fun j=> Daisy.sparkPath ..]; simp only [Sum.inr.injEq]
    apply (payments M Y χ rA hp p).weaken; unfold tune Mixed.selected; rw [if_pos (show Allowed S Q.halo sx X' Y.birth d 0 n 0 p from h)]; unfold Mixed.Price; simp_rw [← hr]; exact le_mul_of_one_le_right (Paid.rocket (payments M Y χ rA hp p)) (show 1 ≤ (1+Y.shapeW p)^k from one_le_pow₀ (le_add_of_nonneg_right (Y.positive_volume p))) -- after rw hr
  have he(p': Tickets (sign M S))(U): act M Y χ U p p'=0:= by
    letI : Nonempty (Forest S.ratio):=Tree.select S.ratio S.patch.odd_side
    by_contra hz; have hp:=(present M Y χ U p' p (F:= Classical.ofNonempty) hz).2
    exact h ⟨hp.1,Nat.zero_le _,hn,Y.positive_volume p⟩
  unfold tune Mixed.selected; rw [if_neg (show ¬Allowed S Q.halo sx X' Y.birth d 0 n 0 p from h)]
  apply Paid.congr paidZero; intro u x hx; ext i; unfold vote color; simp_rw [he, mul_zero, sum_const_zero]; rfl
end YM.Merge.Palette
