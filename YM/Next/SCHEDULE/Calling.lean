import YM.Next.SCHEDULE.Continuing
import YM.Next.SCHEDULE.Levels

/-!
# Hot checks for some of the iterative numerical gates

Not a proof of Advance / Loop! What callers must supply does NOT come
from the trajectory merely running. In particular here fStep must realize
the E and K estimates IN these contribution norms; personal `Funds` about
other/different E,K are not enough. LHS tests on actual absolute label
weights at assigned points. No field-dependent cutoff in the schedule.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Scheduling.Deployment
open Filter RG RG.Supply Function Precision Input Bid Pressure Lattice Source
open Clock Instrument
open scoped Topology

variable {G : Gauge}
lemma clock_eqns (c : Calendar G) (m : ℕ) :
    let x:=c.hatBeta m;
    c.coverSize m=plain.body x ∧ c.monitor m=plain.P x ∧ c.hatCoupling m=gap x ∧
    c.allowance m=δE x ∧ c.forcedAllowance m=plain.w x ∧
      c.loopCap m=2*LevelCost (c.theta (c.J m)) x ∧ c.threshold m=plain.t x := by
  intro x
  have h : c.monitor m=plain.P x := (Clock.watch_two x).symm
  refine ⟨by simp [body,Calendar.coverSize,cover,plain,x],h,rfl,rfl,?_,?_,?_⟩ <;> first
  | unfold Calendar.loopCap; rw [h]; rfl
  | unfold Calendar.forcedAllowance; rw [h]; rfl
  | unfold Calendar.threshold; rw [h]; rfl

variable {s : Survey G} {K : MapPrices} {q : Quote} {e : ℕ → ℕ → Exchange} {v : ℕ → ℕ}
variable {D : Rolls (s.paper q v)} {Θ : Protection D} {W : Delays Θ} {Y : Bar W} {I : Wait Y}
variable {a : Levels G} {B : Beam K D} {F : ℕ → ℕ → Postage}

/-- A next-call path lemma. L powers and incoming actual caps can APPEAR
in the estimate; that functional shape with same constants even on j→j is
important. Used with unmasked analytic estimates (of which some tests are
required in Kin). Curve preservation / matching identities separate. -/
lemma nextPath (h : Paid I a) (g : Prepaid s K q e v) (p : Regime B e F W) (m : ℕ) :
    let j := a.clock.J (m+1); let i := a.clock.J m; let L:ℝ:=(a.S.block m).val
    ∀ T : PathData G, T.Bounds (a.params m).clip (q.widths.emits j i)
      (classicalFee L (q.classicalCost.classic j i) (a.params (m+1)).paths)
      (q.finish.loop j i*L^ (4:ℕ)+(q.finish.loop j i/L^ (2:ℕ))*a.clock.loopCap (m+1)) →
      T.Bounds (a.params m).clip (a.params m).width (a.params m).paths (a.clock.loopCap m) := by
  intro j i L T hT
  obtain ⟨-, -, -, -, -, h1,-⟩ := clock_eqns a.clock m
  obtain ⟨-, -, -, -, -, h2,-⟩ := clock_eqns a.clock (m+1)
  have ht := pulse h p m
  rw [params h m, params h (m+1), h2, ← hat m] at hT
  rw [params h m,h1]
  refine (learns h g m).keep (adj a _) hT ht.emit ht.reset (Real.rpow_pos_of_pos ?_ _).le
  exact wp _ _

lemma topPath (h : Paid I a) (n : ℕ) (T : PathData G)
    (hT : T.Bounds (a.params n).clip (q.widths.launch (a.clock.J n)) (q.classicalCost.beginCost (a.clock.J n)) 0) :
    T.Bounds (a.params n).clip (a.params n).width (a.params n).paths (a.clock.loopCap n) := by
  obtain ⟨-,-,-,-,-,H,-⟩ := clock_eqns a.clock n
  rw [params h n] at *; rw [H]; apply fund_top _ _ _ _ hT
  exact mul_nonneg (by norm_num) (Real.rpow_pos_of_pos (wp _ _) _).le



private lemma kMore {f : Side} {P : Activities G f} {M : BudgetPoint} {u v : ℝ} (hK : P.KBound M u)
    (hu : u ≤ v) : P.KBound M v := by
  obtain ⟨z,hz,H⟩:=hK
  exact ⟨z,hz,fun x => ⟨(H x).1,(H x).2.1,(H x).2.2.trans hu⟩⟩

/-- Numeric tests /HRGv. Anchored E, hits for K. Callers must
produce the strong post-L exp(-rate*p_*^2)-type here, not the `w` type
(as Movement also consumes at same stage). Sound for every triggered band,
physical period and eligible calculation; actual analytic tests assumed AT
these scopes, in particular if repeated same-j. `Δ` invoice of kinetic
coupling reset written with its t'^2 *charge*. -/
lemma recloses (h : Paid I a) (p : Regime B e F W) (m n : ℕ) (β : ℝ) (hb : β ∈ Shoot.band a (m+1)) :
    let C := a.clock; let j:= C.J (m+1); let i:=C.J m; let L:ℝ:=(a.S.block m).val
    let c := (e j i).cost; let f := F j i
    let θ:= C.theta j; let x:= C.hatBeta m; let y:=C.hatBeta (m+1); let g:=gap β
    let H := c*f.switch plain c L θ x y g; let t':= C.threshold m; let t:= C.threshold (m+1)
    ∀ P : Activities G (a.S.side m n),
      P.EBound (a.budget m) (H+f.bundle plain θ x y*t'^ (3:ℕ)) →
      P.KBound (a.budget m) (f.H*Real.exp (-f.rate*(t/g)^ (2:ℕ))) →
      P.EBound (a.budget m) (C.allowance m) ∧
        P.KBound (a.budget m) (Real.exp (-(B.price F).g j * (C.monitor (m+1))^ (2:ℕ))) ∧
        P.KBound (a.budget m) (C.forcedAllowance m) ∧
        ∀ Δ : ℝ, t'^ (2:ℕ)*|Δ| ≤ H → |Δ| ≤ 1 := by
  intro C j i L c f θ x y g H t' t P hE hK
  have ht := pulse h p m
  have hb := ht.budgets β (by rw [hat]; exact trial_in hb)
  have hs := ht.save
  dsimp only at hb ht
  rw [hat] at hb hs; obtain ⟨hb,hc,hz,-⟩ := hb
  obtain ⟨-,-,-,hk,hg,-,hd⟩:=clock_eqns C m
  obtain ⟨-,hx,-,-,-,-,he⟩:=clock_eqns C (m+1)
  have he' : t=plain.t _ := he
  have hd' : t'=plain.t _ := hd
  have hK' : P.KBound (a.budget m) (Real.exp (-(B.price F).g j * (C.monitor (m+1))^ (2:ℕ))) := by
    refine kMore hK ?_; rw [he',hx]; exact hz
  refine ⟨?_, hK', kMore hK' (by rw [hx,hg]; exact hs),?_⟩
  · obtain ⟨A,hA,hA'⟩:=hE
    have hh : H+f.bundle plain θ x y*t'^ (3:ℕ) ≤ C.allowance m := by rw [hk,hd']; exact hb.le
    exact ⟨A,hA,fun x => ⟨(hA' x).1,(hA' x).2.1,(hA' x).2.2.trans hh⟩⟩
  intro Δ hg
  have hz : 0 < t' := (a.budget m).threshold_pos
  change |Δ| ≤ _
  apply le_of_mul_le_mul_left ?_ (sq_pos_of_pos hz)
  exact hg.trans (by rw [mul_one,hd']; exact hc)
end YM.Next.Scheduling.Deployment
