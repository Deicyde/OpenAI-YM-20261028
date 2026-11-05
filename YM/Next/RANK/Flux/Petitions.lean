import YM.Next.RANK.Concord
import YM.Next.RANK.Flux.Conductor


/-!
# Pledges prior to evacuation

One possible way to purchase supplies in Concord. Includes Ticket cadence.
Still requires the E Ranked Step oracle at the requested mode; no grants asserted.
Note actual k-N-anch Sites everywhere -- not Mark.Z on terminal limiting points. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Flux
open Marker Glyph Exponential Finset Lattice Ac Relation Value Corona RG Wilson MeasureTheory Tapes Spindle Atlas Station Peak Cells Perch Edition Filter
open scoped BigOperators Classical Topology

variable {V ι : Type} {G : Gauge} {c : Family G} {N k m i p a q d : ℕ} {x : Points m} {η y b r z φ : ℝ}
variable {S : Era} {R : Lead G c.S p} {X : Course c N p k} {P : (i : ℕ) → Rep G (c.side i p)}

private lemma curtail {X : ℝ} (h : 0 ≤ X) (hp : X ≤ 1) : 0 ≤ Real.exp X-1 ∧ Real.exp X-1 ≤ 2*X:= by
  have hv := sub_nonneg.mpr (Real.one_le_exp h); refine ⟨hv,?_⟩; have hx:= Real.abs_exp_sub_one_le (show |X|≤ 1 from (abs_of_nonneg h).trans_le hp); rwa [abs_of_nonneg hv,abs_of_nonneg h] at hx
-- kinetics tested with walls before actual estimates, uniformly post-L under fixed stage AND before J gates
lemma timing : ∀ᶠ u : ℝ in atTop, ∀ P : BudgetPoint,P.B≤walls u→Tickets P (kinetics u):= by
  filter_upwards [big.eventually_ge_atTop 1, Paint.q_power 4 (1/16) (by norm_num), (Perch.bill_hi (show (-1/8:ℝ)+1/16 < 0 by norm_num)).eventually (ge_mem_nhds (show (0:ℝ)<1/3000 by norm_num)), (bill_hi (show (-1/8:ℝ)<0 by norm_num)).eventually (ge_mem_nhds (show (0:ℝ)<1/50 by norm_num))] with s hW hb hx hv
  intro P h; let C:=kinetics s; let K:ℝ:= walls s; have he:(1:ℝ) ≤ K:= by unfold K; exact_mod_cast hW
  let Z:= ((P.B+P.B+1:ℕ):ℝ)^4
  have hψ : (P.B:ℝ)≤K:= by unfold K; exact_mod_cast h
  have hs: Z ≤ (3*K)^4:= by
    unfold Z; gcongr; push_cast; linarith only [he,hψ]
  have ht : 0 ≤ C:= (Real.exp_pos _).le; have hp:C≤1/50:=hv
  have hZ : Z*C ≤ 81/3000:= by
    apply (mul_le_mul_of_nonneg_right hs ht).trans; rw [mul_pow,mul_assoc]; apply (mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_right hb ht).trans ((le_of_eq (by unfold C kinetics; rw [overlap, add_comm])).trans (le_of_eq_of_le rfl (show bill _ _ ≤ _ from hx)))) (by norm_num : (0:ℝ)≤3^4)).trans; norm_num
  have hh := curtail ht (by linarith only [hp]); let H:=Real.exp C-1; obtain ⟨hx,hv⟩:= hh; change H ≤2*C at hv
  obtain ⟨hG,hL⟩:=curtail (show 0≤H+H from add_nonneg hx hx) (show H+H ≤ 1 by linarith only [hv,hp]); let F:=Real.exp (H+H)-1
  have hb : F+C ≤9*C:=by change F ≤ _ at hL; linarith only [hL,hv]
  have hc : 0 ≤ F+C:= add_nonneg hG ht; have hs:= curtail hc (by linarith only [hb,hp]); have hz : 0 ≤ Z:= by unfold Z;positivity
  refine ⟨⟨ht,hZ.trans (by norm_num)⟩,⟨hx,?_⟩,⟨add_nonneg hx hx,?_⟩,⟨hc,?_⟩,hs.2.trans ?_⟩ <;> first
    | (change Z*(F+C) ≤ 1; linarith only [mul_le_mul_of_nonneg_left hb hz,hZ])
    | (change Z*H ≤1; linarith only [mul_le_mul_of_nonneg_left hv hz,hZ])
    | (change Z*(H+H) ≤1; linarith only [mul_le_mul_of_nonneg_left hv hz,hZ])
    | (change 2*(F+C)≤1; linarith only [hb,hp])

variable (p' : Purse)

structure Choir (p' : Purse) (X : Course c N p k) (Y : (i : ℕ)→ Rep G (c.side i p)) (R : Lead G c.S p) (x : Points m) : Prop where
  rewrites (g : ℕ) (h : g<k) (hk : middle c.path.levels p'.band k ≤ g) :
    let t:= clim c.path.levels k
    ∃ v : Ignition R p'.band x X h hk p'.era.coast.Q p'.horizon (Y (g+1)).p (Y g).p (p'.sends t),
    ∃ B, Audience (S:=p'.era) v B (p'.cash t) p'.goal
  applies j : Station.width c.path.levels p'.band k ≤ j → ∀ h : j < middle c.path.levels p'.band k,
    ∃ B, Dark ((show j+1 ≤ middle c.path.levels p'.band k from h).trans ((before c.path.levels p'.band k).trans X.allow)) X x p'.era p'.band (Ship.allowance c.path.levels 2 k) (Y (j+1)) (Y j) B



-- supplies alternative S.View
variable (F : Cohesion c d) {S₀ : Table c.book} (P₀ : Columns c S₀ d) (H : c.Makes) (O : HaarBudget G)




end YM.Next.Rank.Flux
