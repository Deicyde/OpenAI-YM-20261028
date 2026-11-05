import YM.UVExtension.Concert.Stethoscope
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Song.Embassy

set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Concert
open Filter Function Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open ConnectedActivityE6 Blaze March Push Push.AbsoluteSums Lamppost AnalyticBridge VerifiedReset Collection Quotes Next.Foundations
open PhysicalNext.Repeat Song Extra.Iteration
open scoped Topology BigOperators ContDiff Classical
-- Readable earnings; `Capitol X coin.p` homogeneous Cash. don't assume certificates linear.
variable {G:Gauge} {p:BudgetPoint}{A K : Type} {Z D : Type*} {n:Side} [NormedAddCommGroup Z] [NormedSpace ℂ Z] {Q:Opening D Z}
    {b:ℝ} {e f: Z→ℝ}
variable (Y:A → RegularAddress n) (P:D→ A→ Config G n→ℝ) {α : ℝ}

def fork (p:BudgetPoint)(G:Gauge)(Y:A→ RegularAddress n)(α:ℝ): Meter A (Site n) where
    test i:= Tap p G (Y i).site (Y i).support
    cost i j := if (Y j).site=i then Real.exp (α*coverNumber p.B (Y j).support) else 0
    nonneg i j:= by split <;> positivity
    awake j := ⟨(Y j).site, by rw [if_pos rfl]; exact Real.exp_pos _⟩
def trill (p:BudgetPoint)(G:Gauge)(Y:A→ RegularAddress n)(α:ℝ) (f:A→ Config G n→ℝ):(fork p G Y α).Slot:= fun a i=>Tap.read (show Tap p G (Y a).site (Y a).support from i) (f a)

def ticketR (Q:Opening D Z) (p:BudgetPoint)(Y:A→RegularAddress n)(α:ℝ) (P:D→ A→ Config G n→ℝ)(b:Z→ℝ):= Atlas (fork p G Y α) Q (fun d=>trill p G Y α (P d)) b
attribute [reducible] ticketR

def coinE (p:BudgetPoint)(α:ℝ)(f:A→ℝ)(b:ℝ) := Push.AbsoluteSums.Footprint.Anchored (fun i=> (Y i).site) f (fun i=>coverNumber p.B (Y i).support) α b
lemma singers (g:A→ℝ): (∀ x, SumBudget (fun j=> (fork p G Y α).cost x j*g j) b) ↔ coinE Y p α g b:= by
  unfold coinE Push.AbsoluteSums.Footprint.Anchored
  simp only [fork,ite_mul,zero_mul]; simp only [mul_comm]
lemma fork_earns (F:A→ Config G n→ℝ) : Meter.MeasureP (fork p G Y α) (trill p G Y α F) b ↔ ∃ c:A→ ℝ, (∀ i,p.supBounds (Y i).site (Y i).support (F i) (c i))∧ coinE Y p α c b:=by
  constructor
  · rintro ⟨c,h,hc⟩
    exact ⟨c,fun i=> tap_bound.mpr (h i), (singers (G:=G) Y c).1 hc⟩
  rintro ⟨c,h,hc⟩
  exact ⟨c,fun i=> tap_bound.mp (h i),(singers (G:=G) Y c).2 hc⟩

variable {p' : BudgetPoint} (Y':K→ RegularAddress n)(P':D→ K→ Config G n→ℝ)
abbrev smoothP (p:BudgetPoint)(Y:A→ RegularAddress n)(P:A→ Config G n→ℝ): Prop:= ∀ i,p.Regular (Y i).support (P i)
def plaits (S:Finset D)(a:D→ℝ)(P:D→ A→ Config G n→ℝ)(i:A):Config G n→ℝ:= ∑ j∈S,a j • P j i
lemma blasts (S:Finset D)(a:D→ℝ)(hp:∀ i,smoothP p Y (P i)):smoothP p Y (plaits S a P) := fun i=> brigade S a _ (fun j _=> hp j i)
lemma raises (S:Finset D) (a:D→ℝ) (u:ℝ) (hp:∀ i,smoothP p Y (P i)): (fork p G Y u).MeasureP (fun i k=>∑ j∈S,a j*trill p G Y u (P j) i k) b ↔ ∃ c:A→ℝ, (∀ i,p.supBounds (Y i).site (Y i).support (plaits S a P i) (c i))∧ coinE Y p u c b:=by
  rw [← fork_earns]; apply iff_of_eq; congr 1
  funext i k; let x:Tap p G (Y i).site (Y i).support:=k
  exact (x.staves S a _ (fun j _=> hp j i)).symm
lemma roads {U x w : ℝ} (hp:∀ i,smoothP p Y (P i)) (hq:∀ i,smoothP p' Y' (P' i)) (F:ticketR Q p Y α P f) (ht:∀ z∈Q.span,0≤f z∧f z ≤U)(hU:0≤U)(hx:0 ≤ x)
    (he : ∀ (S0 : Finset D) (a : D → ℝ) (m : ℝ) (c : A → ℝ), 0 ≤ m → (∀ i,p.supBounds (Y i).site (Y i).support (plaits S0 a P i) (c i))→ coinE Y p α c m → ∃ c:K→ℝ, (∀ i,p'.supBounds (Y' i).site (Y' i).support (plaits S0 a P' i) (c i))∧ coinE Y' p' w c (x*m)) : Nonempty (ticketR Q p' Y' w P' (fun z=>4*x*f z)):=
  F.apply_to _ ht hU hx (fun S a m hm h=> by
    obtain ⟨c,hc,hQ⟩:= raises Y P S a _ hp|>.1 h; exact (raises Y' P' S a _ hq).2 (he S a m c hm hc hQ))

lemma revolving {U:ℝ} (hp:∀ i,smoothP p Y (P i)) (F:ticketR Q p Y (preExponent p) P f) (ht:∀ z∈Q.span,0≤f z∧f z ≤U)(hU:0≤U)(hq:∀ i, smoothP p (revolve Y) (choir (P i))) : Nonempty (ticketR Q p (revolve Y) (preExponent p) (fun i=> choir (P i)) (fun z=>4*turnFee p*f z)):= by
  apply roads Y P _ _ hp hq F ht hU (turnFee_pos _).le
  intro S a m c hm h hc
  obtain ⟨hh,hH⟩:= spiral Y _ c (blasts Y P S a hp) h hc
  have hF: plaits S a (fun i=> choir (P i))= choir (plaits S a P) := by
    funext i V; unfold choir plaits; rw [Pi.smul_apply,Function.comp_apply, Finset.sum_apply,Finset.sum_apply,Finset.smul_sum]; apply Finset.sum_congr rfl; intro j _; change a j*(Rim n*_)=Rim n*(a j*_); ring_nf; rfl
  rw [hF]; exact ⟨_,fun i=>(hh i).2,hH⟩

variable {H:ticketR Q p Y α P f} {J: ticketR Q p Y' α P' e}
lemma bundled (H:ticketR Q p Y α P f) (J:ticketR Q p Y' α P' e): Nonempty (ticketR Q p (Sum.elim Y Y') α (fun d=> Sum.elim (P d) (P' d)) (f+e)):=by
  let Z':=Sum.elim Y Y'; let M:= fork p G Z' α
  let F (z:Z): M.CSlot := fun t=> (match t with | Sum.inl i=> H.f z i | Sum.inr i=> J.f z i)
  refine ⟨⟨F,?_ ,?_ , fun z hz=> ?_⟩⟩
  · rintro d (k|k); exact fun i=> H.exacts d _ _; exact fun i=> J.exacts ..
  · rintro (k|k); exact fun i=> H.pulse _ _; exact fun i=> J.pulse _ _
  obtain ⟨u,h,hU⟩:= (H.bounds z hz).afloat; obtain ⟨v,hv,hV⟩:= (J.bounds z hz).afloat
  exact ⟨Sum.elim u v,fun t=>match t with | Sum.inl _=> h _ | Sum.inr _=> hv _,fun i=> Cost.sum (hU i) (hV i)⟩
lemma relocated (k:K≃ A)(H: ticketR Q p Y α P f) : Nonempty (ticketR Q p (Y∘k) α (fun i=> P i ∘ k) f):= by
  refine ⟨⟨fun z t=> H.f z (k t),fun z t i=> H.exacts ..,fun t i=> H.pulse _ _,fun z hz=> ?_⟩⟩
  obtain ⟨u,h,hU⟩:= (H.bounds z hz).afloat; exact ⟨u∘k,fun i=> h _,fun i=> Cost.equiv k (hU i)⟩
lemma broaden (H:ticketR Q p Y α P f) (h:∀ z∈Q.span,f z≤e z) : Nonempty (ticketR Q p Y α P e):= by
  refine ⟨{H with bounds:=fun z hz=>?_}⟩
  obtain ⟨u,hp,hU⟩:= (H.bounds z hz).afloat; exact ⟨u,hp,fun i=> budget_loosen (hU i) (h z hz)⟩
end YM.UVExtension.Concert
