import YM.OPE.Nesting.Comparable

/-!
# Orders filled from homogeneous-scale alternatives

One may vary the auxiliary truncations to make a comparable tray. Costs
transfer back to the SAME full input menu. For its complete remainder, a
further finite debit pays for retesting fields at the actual stated horizon.
It uses price `(D+1)*(k-u)` only when this is a genuine gain.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Nesting
open Orbits Orbits.Reader Function Filter Extraction Set Table Tree Measures Menu Atom MeasureTheory
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G}{F:Order}{S:Table C.book}(U:Spec.Final C F S)
  (R:Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)
variable {L I J:Type} {l:Filter L}{T:L→ℝ}{o:L→E4}{z:L→I→E4}

structure Supply (l:Filter L)(T:L→ℝ)(z:L→I→E4)(k M:ℝ)(A:Menu S L):Prop where
    clients : ∃ b₀:ℝ,k≤b₀ ∧ ∀ b:ℝ,b₀≤b→ (Eligible l T z b A ∧ ∀ (W γ:ℝ), ∃ P:Menu S L,Comparable l T z k M P ∧ Agrees U l T z k b W γ A P)

namespace Supply
variable {A P:Menu S L}
variable {k u M b γ W:ℝ}
variable [Fintype I](h:Services C F S)(hT:Tendsto T l atTop)[l.NeBot]
       (hk:0≤k)(hx:enveloped l T k z o)(hz:Tendsto (fun i=>away (z i) (o i)) l (𝓝 0))(h₀:Supply U l T z k M A)
include h hT hk hx hz
private lemma buys (he:Agrees U l T z k b W γ A P)(hk':k≤b)(hP:Comparable l T z k M P)(ha:Eligible l T z b A){m:ℕ}(hw:Sensor.affordable U R m W)(c:R.channels m): RateLE l T (fun i=>A.charge R m c o i-P.charge R m c o i) γ:=by
    change RateLE l T (fun i=>A.charge R m c o i-P.charge R m c o i) γ -- header .. issue
    exact Sensor.remit U R A P c hw hT (by exact he) ha (hP.earns hk') hz hk hk'
private lemma fromSupply (h':Comparable l T z k M P) : Meets U R l T z o k M P:= Comparable.meets U R hT h hz _ hx hk h'
include h₀
lemma first (m:ℕ)(c:R.channels m):RateLE l T (A.charge R m c o) (M-m*k):=by
    obtain ⟨W,hw⟩:= Sensor.roomFor U R m; obtain ⟨α,ha,hα⟩:= h₀.clients
    let r:=M-m*k; obtain ⟨P,hP,h₂⟩ := (hα α le_rfl).2 W r
    exact ((buys U R h hT hk hx hz (by exact h₂) ha hP (hα _ le_rfl).1 (hw m le_rfl) c).add ((fromSupply U R h hT hk hx hz hP).output m c) hT).congr (Eventually.of_forall fun _=> sub_add_cancel ..)

variable [Fintype J](y:L→J→E4)(w:J→S.Tag)(m:ℕ)(s:L→Viewers U)
lemma last (hy:Kept l T b y)(h₁:Intervals l T u (fun l=>sole (o l)) y)(h₂:Intervals l T u z y)(hu:0≤u)(hb:u≤b)(hu':u ≤ k):RateLE l T (delta U R A m o s w y) (M-((m+1:ℝ)*(k-u))+weightOf w*b):=by
    obtain ⟨W,hw⟩:= Sensor.roomFor U R m; let W':=max W (weightOf w); obtain ⟨α,ha,hα⟩:= h₀.clients
    let B:=max α b; let r:=M-((m+1:ℝ)*(k-u)); let γ:=r-m*u
    obtain ⟨P,hP,h_c⟩:= (hα B (le_max_left ..)).2 W' γ; let e:=r+weightOf w*b
    have h_y:=hy.mono (le_max_right α b)
    have hf(n)(h_n:n ≤ m)(c:R.channels n): RateLE l T (fun i=>A.charge R n c o i - P.charge R n c o i) γ:= by apply buys U R h hT hk hx hz (W:=W') (b:=B) (show Agrees U l T z k B W' γ A P from h_c) (ha.trans (le_max_left ..)) hP (hα B (le_max_left ..)).1 (fun j hj t ht=> (hw n h_n j hj t ht).trans (le_max_left ..))
    let f (j:Menu.Cut R m)(i:L) := soloView U R j.fst j.snd (o i) (s i) w (y i)
    have h₀ : RateLE l T _ e:= (h_c w y s (le_max_right ..) (h₂.mono hu') h_y).mono (le_trans (sub_le_self r (mul_nonneg m.cast_nonneg hu)) (le_add_of_nonneg_right (mul_nonneg (weightOf_nonnegative w) (hu.trans hb))))
    let h(j:Menu.Cut R m)(i:L):= (A.charge R j.fst j.snd o i - P.charge R j.fst j.snd o i)*f j i
    refine ((h₀.add (fromSupply U R ?cert hT hk hx hz hP|>.tested w y m s b u hy h₁ h₂ hu hb hu') hT).sub (RateLE.sum (f:=h) (S:=Finset.univ) hT ?_) hT).congr (Eventually.of_forall fun i=>?_)
    case cert=> assumption
    · intro j (_:j∈(Finset.univ:Finset (Menu.Cut R m))); have hh:= (hf j.1.val (Nat.le_of_lt_succ j.1.isLt) j.snd).mul (pulse_single (w:=w) (s:=s) U R (h:= by assumption) hT j.2 h₁ hy hu hb)
      exact hh.mono (show γ+(j.1.val*u + weightOf w*b) ≤ e from by
          have hg: (j.1.val:ℝ) ≤ m:=by exact_mod_cast Nat.le_of_lt_succ j.1.isLt
          dsimp only [e,γ]; linarith only [mul_le_mul_of_nonneg_right hg hu]) -- fromSupply shadow named h issue
    dsimp only; unfold delta h
    simp_rw [sub_mul,Finset.sum_sub_distrib]; dsimp [f]; change (_-_)+(_-_) - (_-_) = (_-_:ℂ); abel

omit [Fintype J] in
lemma achieves :Meets U R l T z o k M A:= ⟨first U R h hT hk hx hz h₀,fun w y m s _ _=> by apply last U R h hT hk hx hz h₀⟩
end Supply
end YM.OPE.Nesting
