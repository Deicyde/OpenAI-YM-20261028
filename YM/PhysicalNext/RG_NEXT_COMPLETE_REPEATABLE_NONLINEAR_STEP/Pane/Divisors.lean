import YM.Price.Waits

/-!
# Divisible periods variation of Wait.ready (uses its proof)

Only numeric logic of an advance satisfying every finite request at stage.
No implication that the requests have been yet mapped to a mathematical RG
argument. First plateau fixed. Works at all periods, initial smaller spacings
not assumed.
-/

set_option autoImplicit false
noncomputable section
namespace YM.RG.Supply

open Wilson Lattice Set Filter Function Asymptotics Finset Real
open scoped Matrix.Norms.Frobenius Topology BigOperators ContDiff

variable {G : Gauge} {p : Sheet G} {w : Rolls p} {T : Protection w} {W : Delays T} {Y : Bar W}

def AsDivisors (S : Schedule) := ∀ c : Side, ∀ z, ∃ p≥z, c.val ∣ (S.period p).val
variable (B : Wait Y) (hh : G.Simple)
include hh B

/-- Issue all the requests. -/
theorem Wait.engine : ∃ a : Levels G, Paid B a ∧ AsDivisors a.S := by
  have h (j : ℕ) : p.first < p.first+(j+1) := by omega
  choose b Hb using fun j => Y.enters hh (h j)
  choose c Hc using fun i => B.lead (p.first+i)
  obtain ⟨E,HA,HB⟩ := Program.exhaust (fun i => b (i-1)) c
  let s := E.extent w
  have big (i : ℕ) (ha : E.J (i+1) > 0) :
      let j:=p.first+E.J (i+1)
      W.betaEntry j ≤ Y.value+G.slopeConstant*s i ∧ W.scaleEntry j Y.value ≤ s i ∧
      0 < s i ∧ Real.log (w.L j).val ≤ (j:ℝ)⁻¹*s i ∧ (Y.bill j (s i):ℝ) ≤ Real.exp (s i) := by
    intro j; have hk := HA i ha
    unfold j; cases he : E.J (i+1) with
    | zero => omega
    | succ j => exact Hb _ _ (by simpa only [he,Nat.add_sub_cancel] using hk) _ (E.scaled_lower w i)
  obtain ⟨n,hn⟩ := eventually_atTop.1 (E.forever.eventually (eventually_ge_atTop 1))
  let M := B.minLength + (range (n+1)).sup (fun i => Y.bill p.first (s i))
  let A := E.book M Y
  have e (i) : A.schedule.scale i = s i := E.extent_scale ..
  have h0 (j) : 3 ≤ (A.schedule.block j).val := A.schedule.block_large j
  have hge (j) : Y.value ≤ A.hatBeta j := by
    unfold Calendar.hatBeta
    rw [e]
    have h₁ := (E.scaled_lower w j)
    have h₂ : 0 ≤ s j := le_trans (mul_nonneg (by positivity) (Real.log_nonneg (by norm_num))) h₁
    exact le_add_of_nonneg_right (mul_nonneg (Gauge.slopeConstant_pos hh).le h₂)
  have vol (i k) :
      let F := W.shells (A.J (i+1)) * (1+A.coverSize i+A.coverSize (i+1))^(W.growth (A.J (i+1)))
      F ≤ (A.schedule.side i k).val ∧ 100*(A.coverSize i+1) ≤ (A.schedule.side i k).val ∧
      100*((A.op i k).patch.radius+1) ≤ (A.schedule.side (i+1) k).val := by
    intro F
    have e1 : Nat.ceil (Real.log (Y.value+G.slopeConstant*s i)^2) = A.coverSize i := by
      unfold Calendar.coverSize Calendar.hatBeta; rw [e]; rfl
    have e2 : Nat.ceil (Real.log (Y.value+G.slopeConstant*(s i+Real.log (w.L (A.J (i+1))).val))^2) = A.coverSize (i+1) := by unfold Calendar.coverSize Calendar.hatBeta; rw [e]; rfl
    have bill : Y.bill (A.J (i+1)) (s i) = F+100*(A.coverSize i+1)+100*((A.op i k).patch.radius+1) := by rw [Bar.bill,e1,e2]; rfl
    have hi : Y.bill (A.J (i+1)) (s i) ≤ (A.schedule.side i k).val := by
      by_cases he : E.J (i+1)=0
      · have hx : i < n+1 := by
          by_contra! hi
          have hv : 1 ≤ E.J (i+1) := hn _ (by omega); omega
        have hz : A.J (i+1)=p.first := by change _+E.J (i+1)=_; rw [he,Nat.add_zero]
        rw [hz]
        have he : Y.bill p.first (s i) ≤ M := le_trans (le_sup (f:=fun i => Y.bill p.first (s i)) (mem_range.mpr hx)) (Nat.le_add_left ..)
        change _ ≤ 4*(M+k+1)*(A.schedule.denominator i).val
        have hb : Y.bill p.first (s i) ≤ 4*(M+k+1) := by omega
        exact hb.trans (Nat.le_mul_of_pos_right _ (A.schedule.denominator i).property)
      have he := (big i (Nat.pos_of_ne_zero he)).2.2.2.2
      have hp : Real.exp (s i) = (A.schedule.denominator i).val := by
        rw [← e]; unfold Schedule.scale Schedule.a
        rw [inv_inv, Real.exp_log (by positivity)]
      rw [hp] at he
      apply le_trans (b := (A.schedule.denominator i).val) (by exact_mod_cast he)
      exact Nat.le_mul_of_pos_left _ (A.schedule.period k).property
    have hl : (A.schedule.side i k).val ≤ (A.schedule.side (i+1) k).val := Nat.mul_le_mul_left _ (A.schedule.den_strict.monotone (Nat.le_succ i))
    omega
  have hJ : Monotone A.J := fun i j hij => Nat.add_le_add_left (E.mono hij) p.first
  have hJ' : Tendsto A.J atTop atTop := tendsto_atTop_mono (fun i => Nat.le_add_left ..) E.forever
  have hj (i) : p.first ≤ A.J i := Nat.le_add_right ..
  have hb : A.Fits :=
    { delayed := fun m => Y.good.trans_le (hge m)
      smallField := fun m => Y.threshold _ (hge m)
      sizeT := fun m i => (vol m i).2.1
      fitsPatch := fun m i => (vol m i).2.2
      sameFactor := fun _ => rfl
      monotoneL := w.grow
      mono := hJ
      stepSlow := fun i => by change p.first+_ ≤ p.first+_+_; rw [Nat.add_assoc]; exact Nat.add_le_add_left (E.up i) _
      deep := hJ'
      deepOrder := p.orders.comp hJ
      deepPower := p.powers.comp hJ
      deepExp := p.prices.comp hJ
      driftSmall := fun m => (w.large (A.J (m+1))).slow (hj _)
      logCost := fun m => (w.large (A.J (m+1))).fits (hj _)
      thetaRange := fun m => ⟨T.pos _,T.small _ (hj _)⟩
      thetaMono := T.dec
      mesh := by
        refine squeeze_zero' ?_ ?_
          (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp (hJ'.comp (tendsto_add_atTop_nat 1))))
        · filter_upwards [A.schedule.divergent.eventually (eventually_ge_atTop (0:ℝ))] with i hi
          exact div_nonneg (Real.log_nonneg (by exact_mod_cast (show 1 ≤ (A.schedule.block i).val from le_trans (by norm_num) (h0 i)))) hi
        filter_upwards [eventually_ge_atTop n] with i hi
        have h := big i (Nat.succ_le_iff.mp (hn _ (by omega : n ≤ i+1)))
        change Real.log ((A.schedule.block i).val:ℝ)/ A.schedule.scale i ≤ ((A.J (i+1):ℝ))⁻¹
        rw [e,div_le_iff₀ h.2.2.1]; exact h.2.2.2.1 }
  refine ⟨⟨A,hb,A.blocks_go p.has⟩, ⟨rfl,rfl,rfl,by change p.first+E.J 0=_; rw [E.starts,Nat.add_zero],
    by change p.first+E.J 1=_; rw [E.one,Nat.add_zero],rfl,rfl,?_,?_,?_,fun m i => (vol m i).1,?_⟩,?_⟩
  · intro m; change W.betaEntry (A.J (m+1)) ≤ A.hatBeta m
    by_cases he : E.J (m+1)=0
    · have hx : A.J (m+1)=p.first := by change p.first+E.J (m+1)=_; rw [he,Nat.add_zero]
      change W.betaEntry (A.J _ ) ≤ _; rw [hx]; exact Y.ready.trans (hge m)
    unfold Calendar.hatBeta; rw [e]; exact (big _ (Nat.pos_of_ne_zero he)).1
  · intro m hm; change W.scaleEntry _ _ ≤ A.schedule.scale m; rw [e]; apply (big m ?_).2.1; change p.first < p.first + E.J (m+1) at hm; omega
  · intro i; change B.minLength ≤ 4*(M+i+1); have : B.minLength ≤ M := Nat.le_add_right ..; omega
  · intro j hj
    obtain ⟨i,rfl⟩ := Nat.exists_eq_add_of_le hj
    obtain ⟨k,hk,H⟩ := HB i
    have hg : E.J k=i := H _ (by omega) (by omega)
    have he := E.scaled_upper w k; rw [hg] at he
    have ht := Hc i k hk (s k) (E.scaled_lower w k) he
    refine ⟨k,?_,?_,?_⟩
    · rw [show Levels.S _=A.schedule from rfl,e]; exact ht.1
    · rw [show Levels.S _=A.schedule from rfl,e]; exact ht.2.trans (Nat.div_le_self ..)
    rw [show Levels.S _=A.schedule from rfl,e]
    intro a ha hh; change p.first+E.J a=_; exact congr_arg _ (H _ (by have := ht.2; omega) (hh.trans (Nat.add_le_add_left ht.2 _)))
  intro c z
  let p := c.val * (M+z+1)-(M+1)
  have hc : 1 ≤ c.val:= c.property
  have hf : M+z+1≤ c.val*(M+z+1) := Nat.le_mul_of_pos_left _ hc
  refine ⟨p,by unfold p; omega,?_⟩
  change c.val ∣ 4*(M+p+1)
  rw [show M+p+1=c.val*(M+z+1) by unfold p; omega]; exact dvd_mul_of_dvd_right (dvd_mul_right ..) _
end YM.RG.Supply
