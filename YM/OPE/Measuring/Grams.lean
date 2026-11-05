import YM.OPE.Measuring.Joined

/-!
# Actual finite position tests with a two-sided price in a leading frame

Auxiliary measuring lengths are those of `Next.UVStress.Approaches` on
the weak X-space comparison (`Measuring.simultaneous` above). These bounds
are with its own measuring labels **inside** the actual correlations, here
only unselected first, not fixed-field asymptotics yet. We isolate the actual
finite tests, as distinct from a free-matrix inverse assumption on every period
or on every unmeasured size. Same filtration, no Abelian identification of the
theory. More work needed for full polynomial log control in that basis.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Measuring
open Set Function Filter MeasureTheory Analysis Extraction Table Ward Climb Org Spec Next.UVStress
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius

section Linear
variable {V R : Type*}[NormedAddCommGroup V][NormedSpace ℂ V][FiniteDimensional ℂ V]
      [NormedAddCommGroup R][NormedSpace ℂ R][FiniteDimensional ℂ R]
      {S:Type*}{l:Filter S}

lemma priced {A:S→V→ₗ[ℂ]R}{T: V→ₗ[ℂ]R}(hT: ∀ x:V,Tendsto (fun i=>A i x) l (𝓝 (T x)))
        (h:Injective T) : ∃ c:ℝ,1 ≤ c ∧ ∀ᶠ i in l, ∀ x:V, ‖A i x‖ ≤ c*‖x‖ ∧ ‖x‖ ≤ c*‖A i x‖ :=by
    let f (M:V→ₗ[ℂ]R) := LinearMap.toContinuousLinearMap M
    have h₁:=Dash.fit_plane _ _ hT
    obtain ⟨B,hB⟩:= LinearMap.exists_leftInverse_of_injective T (LinearMap.ker_eq_bot_of_injective h)
    let P:= LinearMap.toContinuousLinearMap B; let K:ℝ:=1+‖P‖; let c:=‖f T‖ + 2*K
    have hk:1 ≤ K := by dsimp only [K]; linarith only [norm_nonneg P]
    have h₂:Tendsto (fun i=>‖f (A i)-f T‖) l (𝓝 0) := by simpa [f] using ((h₁.sub_const (f T)).norm)
    refine ⟨c, show 1 ≤ c from by dsimp only [c]; linarith only [hk,norm_nonneg (f T)],?_⟩
    filter_upwards [h₁.norm.eventually (gt_mem_nhds (show ‖f T‖ < c by unfold c; linarith)), h₂.eventually (gt_mem_nhds (show 0 < 1/(2*K) by positivity))] with i hi hd x
    have hp : ‖T x-A i x‖ ≤ (1/(2*K))*‖x‖:= by
       rw [norm_sub_rev]; apply (ContinuousLinearMap.le_opNorm (f (A i) - f T) x).trans (mul_le_mul_of_nonneg_right hd.le (norm_nonneg _))
    constructor
    · apply ((f (A i)).le_opNorm x).trans (mul_le_mul_of_nonneg_right hi.le (norm_nonneg _))
    have he:T x= T x-A i x + A i x := (sub_add_cancel ..).symm
    have hnorm : ‖x‖ ≤ K*‖T x‖:=by
       nth_rw 1 [show x=B (T x) from (LinearMap.congr_fun hB x).symm]
       exact (P.le_opNorm _).trans (mul_le_mul_of_nonneg_right (by unfold K; linarith) (norm_nonneg _))
    have h' := hnorm.trans (mul_le_mul_of_nonneg_left ((show ‖T x‖ ≤ ‖T x - A i x‖+‖A i x‖ from (congr_arg norm he).trans_le (norm_add_le ..)).trans (add_le_add_left hp _)) (zero_le_one.trans hk))
    have hr:K * ((1/(2*K))*‖x‖)=‖x‖/2:=by
      field_simp [ne_of_gt (zero_lt_one.trans_le hk)]
    rw [mul_add,hr] at h' -- avoid unfold?
    unfold c
    linarith only [h',mul_nonneg (norm_nonneg (f T)) (norm_nonneg (A i x))]

end Linear

variable {G : Gauge}{C : Family G}{S : Table C.book}{F : Order}
      (U:Final C F S)(X:Scaling S)(h:Approaches (path X) (isoPanel X))(a:(Bel C.book).Hierarchy)

def put (M : MeterTest (Bel C.book)) (k : ℕ): MeterTest S := ⟨M.n,M.t,panels (isoPanel X k) ∘ M.q⟩
def checks (s:Finset (MeterTest (Bel C.book))) (k d : ℕ) (x:S.Field d) (i:s): ℂ:=
     (put X i.1 k).checkAt U.room.kernel.smooth d (X.r k) (X.positive k) x
include a h
lemma weak_probe (d:ℕ) : ∃ (s:Finset (MeterTest (Bel C.book))) (c:ℝ),1 ≤ c ∧ ∀ᶠ k in atTop, ∀ x:S.Field d, ‖(X.U k d).symm x‖ ≤ c*‖checks U X s k d x‖ ∧ ‖checks U X s k d x‖ ≤ c*‖(X.U k d).symm x‖:=by
   obtain ⟨s,hs⟩:= MeterTest.detects (Bel C.book) a d
   obtain ⟨c,hc,hM⟩:= priced (A:=fun k=>LinearMap.pi fun m:s=> MeterTest.rescaled U.room.kernel.smooth (isoPanel X k) m.val (X.r k) (X.positive k) d) (T:=LinearMap.pi (fun y:s=>y.val.zeroScale a.smooth d)) (fun x=> tendsto_pi_nhds.mpr fun m: s =>MeterTest.reads_limit U.room.kernel.smooth a.smooth h m.val d x) hs
   refine ⟨s,c,hc,?_⟩
   filter_upwards [hM] with k hk x; obtain ⟨h₁,h₂⟩:= hk ((X.U k d).symm x)
   change _ ≤ _*‖checks U X s k d (X.U k d ((X.U k d).symm x))‖ at h₂; change ‖checks U X s k d (X.U k d ((X.U k d).symm x))‖ ≤ _ at h₁
   rw [LinearEquiv.apply_symm_apply] at h₂ h₁; exact ⟨h₂,h₁⟩
end YM.OPE.Measuring
