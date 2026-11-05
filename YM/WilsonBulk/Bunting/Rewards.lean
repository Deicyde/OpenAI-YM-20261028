import YM.WilsonBulk.Bunting.Divides
import YM.WilsonBulk.Broadcast.Court

/-!
# Proxy: prove Ward descent under period enlargements on exact hull

`Test` splits cylinder multiple fields and legs; per-cell mean not a cost
estimate. Allows coefficients of gauge variation nonlinear & analytic tags
written in full Tape through arbitrary finite orders. PowerSeries coefficient
limit through `lcoeff`. No exchanging a weak actual expectation or infinite
Taylor derivative!
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Sheet.Hallmark
open Function Equiv Finset Filter Lattice Laurent Bloch Pert.Bulk Matrix
open AnalyticNext.QuarticMatch.Sheets
open scoped Classical Topology BigOperators ENNReal
open MvPolynomial (X C)
open PowerSeries (coeff constantCoeff)
variable {α β : Type} [Fintype α] {D : ℕ→Side} {c f : Side} {p : Tape α} {n e j : ℕ}

abbrev test (z : β →₀ ℕ) (e : ℕ) : Tape β →ₗ[ℝ] ℝ := (MvPolynomial.lcoeff ℝ z).comp ((coeff (R:=Formula β) e).restrictScalars ℝ) -- spelling
lemma shipping_test (v w : α → Tape β) (I : Record α) (j : ℕ) (z : β →₀ ℕ) :
    test z j (submit v (volumeTape I)-submit w (volumeTape I))=
    ∑ n∈range (j+1), ∑ i∈allowed n,test z j (submit v (PowerSeries.X^n * PowerSeries.C (script (I n i))) - submit w (PowerSeries.X^n * PowerSeries.C (script (I n i)))) := by
  let P:= volumeTape I
  have he : Steps (j+1) P (∑ n∈range (j+1),∑ i∈allowed n,PowerSeries.X^n * PowerSeries.C (script (I n i))) := by
    have ht := before_end (j+1) P; unfold P at *; simpa only [tape_power,capsule,map_sum,mul_sum] using ht
  have hz {α : Type} {p p' q q' : Tape α} (h : Steps (j+1) p q) (h' : Steps (j+1) p' q') : coeff j (p-p')=coeff j (q-q') := by rw [map_sub,map_sub,h j (by omega),h' j (by omega)]
  rw [show test z j _ = test z j ((submit v _) - submit w _) from congr_arg (MvPolynomial.lcoeff ℝ z) ((hz (he.push (submit v) (by rw [submit_X,PowerSeries.constantCoeff_X])) (he.push (submit w) (by rw [submit_X,PowerSeries.constantCoeff_X]))))]; simp only [map_sum, ← sum_sub_distrib, ← Finset.sum_sub_distrib]
-- avoid request big support & infinite rank0
variable (h : c.val∣ f.val)
variable (v w : Co c α→Tape β)
def scales {α : Type} [Fintype α] (V W : α→Tape β) (z : β→₀ ℕ) (j n : ℕ) : Page α e →ₗ[ℝ] ℝ where
  toFun U:=test z j (submit V (PowerSeries.X^n * PowerSeries.C (script U))-submit W (PowerSeries.X^n * PowerSeries.C (script U)))
  map_add' v w:= by rw [script_plus]; simp only [map_add,map_sub,mul_add]; abel
  map_smul' s v:= by rw [script_scale, show PowerSeries.C (s • script v)= s • PowerSeries.C (script v) from map_smul (post _) s _]; simp; ring
omit [Fintype α] in
lemma copied (x : Co c α→ Tape β) (U : Formula (Co f α)) (e : ℕ) : submit x (PowerSeries.X^e * PowerSeries.C (MvPolynomial.rename (harbor α h) U))=submit (x ∘ harbor α h) (PowerSeries.X^e*PowerSeries.C U) := by
  simp only [map_mul,map_pow,submit_C,submit_X]; congr 1; rw [MvPolynomial.aeval_rename]
lemma scale_down (V : Text α (n+1)) (U : Page (Co f α) (n+1)) {σ K : ℝ} (hp : Orates (small f α) V U) (hs : Pervasive V) (hq : Within (lawn α) σ K V) (he : 0≤σ) (z : β→₀ ℕ) :
    scales (v ∘ harbor α h) (w ∘ harbor α h) z e j U=mult h • scales v w z e j (coupon c _ V) := by
  have hf := rename_hush h hp (coupon_reads c hs) hq he
  dsimp only [scales,LinearMap.coe_mk, AddHom.coe_mk]
  rw [← copied h v,← copied h w,hf,map_nsmul,mul_smul_comm,map_nsmul,map_nsmul,← smul_sub,map_nsmul]
lemma size_zero {α : Type} [Fintype α] (i j : ℕ) (V W : α→Tape β) (u : Page α 0) (z : β→₀ ℕ) : scales (e:=0) V W z i j u=0 := by simp only [scales,script_scalar,map_sub,map_mul,map_pow,submit_X,submit_C,MvPolynomial.aeval_C,LinearMap.coe_mk,AddHom.coe_mk]; abel
variable {h : c.val∣ f.val}
variable (hu : ∀ i,c.val∣ (D i).val)
lemma Proxy.scale_down (z : β →₀ ℕ) (i j : ℕ) {u : Text α n} {V : Leaf D α n} (hn : n≠0→ Proxy V u) :
    Tendsto (fun k=> (mult (hu k):ℝ)⁻¹ * scales (v ∘ harbor α (hu k)) (w ∘ harbor α (hu k)) z i j (V k)) atTop (𝓝 (scales v w z i j (coupon c _ u))) := by
  cases n; · simp_rw [size_zero,mul_zero]; exact tendsto_const_nhds
  obtain ⟨σ,p,hx,f,hf,H⟩:= hn (by omega)
  refine ((scales v w z i j).toContinuousLinearMap.continuous.continuousAt.tendsto.comp (tendsto_pi_nhds.mpr fun i=> coupon_limit (H.mono fun u h=> h.2.1) hx hf i)).congr' (H.mono fun k h=>?_)
  change scales v w z i j (coupon c _ (f k))=(mult (hu k):ℝ)⁻¹ * scales (v ∘ harbor α _) (w∘ harbor α _) z i j (V k)
  rw [scale_down (hu k) v w _ _ h.2.2 h.1 h.2.1 hx.le z,nsmul_eq_mul,inv_mul_cancel_left₀ (Nat.cast_ne_zero.mpr (mult_pos _).ne')]
lemma respite (z : β→₀ ℕ) (i : ℕ) {J : ∀ i, Record (Co (D i) α)} {U : Record (Market α)} (hx : dean D J U) :
    Tendsto (fun j=> (mult (hu j):ℝ)⁻¹ * test z i (submit (v ∘ harbor α (hu j)) (volumeTape (J j)) - submit (w ∘ harbor α (hu j)) (volumeTape (J j)))) atTop
      (𝓝 (test z i (submit v (volumeTape (issue c U))-submit w (volumeTape (issue c U))))) := by
  simp_rw [shipping_test,mul_sum]; refine tendsto_finsetSum _ fun j _=>tendsto_finsetSum _ fun n _=>?_ -- unused explicit i fix
  exact Proxy.scale_down v w hu z i j (hx j n)
lemma tribute {J : ∀ i,Record (Co (D i) α)} {U : Record (Market α)} (h : dean D J U)
    (hz : ∀ᶠ j in atTop,submit (v ∘ harbor α (hu j)) (volumeTape (J j))=submit (w ∘ harbor α (hu j)) (volumeTape (J j))) : submit v (volumeTape (issue c U))=submit w (volumeTape (issue c U)) := by
  apply sub_eq_zero.mp; ext i z
  change test z i (submit v (volumeTape (issue c U))-submit w (volumeTape (issue c U)))= (MvPolynomial.coeff z (coeff i (0:Tape β)))
  rw [map_zero,MvPolynomial.coeff_zero]; exact tendsto_nhds_unique_of_eventuallyEq (respite v w hu z i h) (tendsto_const_nhds (x:=(0:ℝ))) (hz.mono fun i hh=> by dsimp only; rw [hh,sub_self,map_zero,mul_zero])
end YM.WilsonBulk.Sheet.Hallmark
