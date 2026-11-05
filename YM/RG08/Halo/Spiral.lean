import YM.RG08.Halo.Base

/-! # Fee schedules before L at every homogeneous sub-coefficient.
`Book'` seismic. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Halo
open Forms Function Finset Jetty Lattice Isles Pert.Bulk Stationary Spar Camera Glyph Filter Laurent RG Precision Exterior Skiff Trickle Weald Hatch Carrel Quarry
open Planned.PrimaryIntegral295 Place Carrier Flint Lagoon Yurt Next.Free
open scoped Classical ContDiff BigOperators Topology ENNReal
variable {G:Gauge}{I J:Type}{n p:ℕ}{u D C:ℝ}

/-- Announced BEFORE L, same h. -/
lemma glossary (n:ℕ):∃ C:ℝ,1≤C∧∀ (f:Pearl){u D:ℝ},0<u→ Pool u n 0 f.val D → ∃ q:(i:Fin n)→Cargo i.val→ℝ,
 f=∑ i:Fin n,∑ j: Cargo i.val,q i j • Lagoon.pal j ∧ ∀ i j,|q i j|≤ C*D*u^i.val:=by
 obtain ⟨C,hC,H⟩:= disclose ℝ n
 refine ⟨C,hC,fun f u D hu hf=>?_⟩
 obtain ⟨g,hg,hw⟩:=Halo.reading f.val hf.band
 have hi := H g hg (hw.symm ▸ hf) hu
 let q(i:Fin n)(j:Cargo i.val):ℝ:=g i (basis ∘ j)
 refine ⟨q,Subtype.ext ?_,?_⟩
 · rw [←hw];unfold mix
   simp only [Submodule.coe_sum]; apply sum_congr rfl; intro i _;funext x; rw [Lagoon.diagonal,Finset.sum_apply];rfl
 intro i j;rw [←Real.norm_eq_abs];refine ((g i).le_opNorm (basis ∘ j)).trans ?_;simp only [Function.comp_apply,basis_norm,prod_const_one,mul_one];simpa only [Nat.zero_add] using hi i

lemma parcel (G:Gauge)(n:ℕ):∃ C:ℝ,1≤C∧∀ (f:Masked G){u D:ℝ},0<u → Pool u n 1 f D → ∃ q:Fin n→Masked G,
 f=∑ i:Fin n,q i ∧ ∀ i, Chit G (i.val+1) (q i) (C*D*u^(i.val+1)):=by
 obtain ⟨C,hC,H⟩:= disclose (Loc G 1→ℝ) n
 refine ⟨C,hC,fun f u D hu hf=>?_⟩
 obtain ⟨g,hg,hw⟩:=Halo.reading f hf.band
 have hi := H g hg (hw.symm ▸ hf) hu
 refine ⟨fun i=>Tensor.diagonal (g i),hw.symm,fun i=>⟨Place.exact_le_band (Nat.lt_succ_self _) (Place.simple (g i)),by have h:=hf.nice;positivity,fun x=>?_⟩⟩
 have hx:‖Tensor.diagonal (g i) x‖ ≤ ‖g i‖ * ‖x‖^i.val:=by simpa only [Tensor.diagonal,prod_const,card_univ,Fintype.card_fin] using (g i).le_opNorm (fun _=>x)
 refine hx.trans (mul_le_mul (by simpa only [Nat.add_comm] using hi i) ?_ (pow_nonneg (norm_nonneg _) _) (by have h:=hf.nice;positivity))
 exact (pow_le_pow_left₀ (norm_nonneg _) (le_add_of_nonneg_left zero_le_one) _).trans (pow_le_pow_right₀ (le_add_of_nonneg_right (norm_nonneg _)) (by omega))
lemma chitQual {f:Masked G}(hf:f∈Place.rangeLt _ n):∃ C:ℝ,Chit G n f C:= by obtain ⟨c,hc,hx⟩:=Place.band_growth hf;exact ⟨c,hf,hc,hx⟩
lemma poolQual (n:ℕ)(f:Pearl)(hf:f.val∈Place.rangeLt ℝ n):∃ C:ℝ,Pool 1 n 0 f.val C:=by
 obtain ⟨c,hc,hx⟩:=Place.band_growth hf;exact ⟨c,hf,hc,fun i=>by simpa using hx i⟩

lemma pal_true (s:Cargo n): (pal s).val∈Place.exactDegree ℝ n:=by
 let f:=pal s
 apply Place.exact_of_smooth ((Pearl.order _ _).contDiffAt)
 intro x t;change profile s (t • x)=_;unfold profile;simp only [PiLp.smul_apply,smul_eq_mul,prod_mul_distrib,prod_const,card_univ,Fintype.card_fin];rfl
lemma pal_charge (s:Cargo n)(x:E4):‖(pal s).val x‖ ≤ ‖x‖^n:=by
 unfold pal profile
 rw [Real.norm_eq_abs, Finset.abs_prod]
 calc
  ∏ i:Fin n, |x (s i)| ≤ ∏ _i:Fin n, ‖x‖ := by
    exact prod_le_prod (fun i _=>abs_nonneg _) (fun i _=>PiLp.norm_apply_le x (s i))
  _ = ‖x‖^n := by simp
-- test formula after polynomial pull. difference top (s degree n) in u^n pack. charge scales all terms
lemma pal_pull (s:Cargo n)(u:ℝ)(v:E4)(hu:0≤u)(hv:u≤1)(hx:‖v‖≤4):
 let f:= aisle u v (pal s)
 ; Pool u (n+1) 0 f.val (5^n) ∧ (f-u^n • pal s:Pearl).val∈Place.rangeLt ℝ n:=by
 intro f
 have huI : u ∈ Set.Icc (0:ℝ) 1 := ⟨hu,hv⟩
 let g:E4→ℝ := (pal s).val
 have he:g∈Place.rangeLt ℝ (n+1):= Place.exact_le_band (Nat.lt_succ_self _) (pal_true s)
 -- precomposition by t scaling closure, preserve band.
 have hk{q:E4→ℝ}{n:ℕ}(H:q∈Place.rangeLt ℝ n): (fun z:E4=>q (u • z))∈Place.rangeLt ℝ n:=by
    obtain ⟨y,hy,hY⟩:=Place.range_decompose H
    rw [hY];simp_rw [Finset.sum_apply];simp_rw [Place.exact_scale (hy _)]
    rw [show (fun z=> ∑ i:Fin n,u^i.val • y i z)=∑ i:Fin n,u^i.val • y i by funext z;rw [Finset.sum_apply];rfl];exact Submodule.sum_mem _ fun i _=>Submodule.smul_mem _ _ (Place.exact_le_band i.isLt (hy i))
 let q(x:E4):=g (x+v)
 refine ⟨⟨hk (q:=q) (band_shift he v),by positivity,fun y=>?_⟩,?_⟩
 · apply (pal_charge s (u • y+v)).trans
   let t:=1+u*‖y‖;have ht:1≤t:=le_add_of_nonneg_right (mul_nonneg huI.1 (norm_nonneg y))
   have hs : ‖u • y + v‖ ≤ 5*t:=by have h:=norm_add_le (u • y) v;rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg huI.1] at h;unfold t at *; linarith only [h, hx, ht]
   rw [pow_zero,mul_one,show (1+u*‖y‖)=t from rfl];refine (pow_le_pow_left₀ (norm_nonneg _) hs n).trans ?_
   rw [mul_pow];exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht (by omega)) (by positivity)
 rw [show (f-u^n • pal s:Pearl).val=(fun x=>(q-g) (u • x)) from ?_];swap
 · funext z;rw [Pi.sub_apply,Place.exact_scale (f:=g) (pal_true s)];rfl
 exact hk (q:=q-g) (Place.pure_step (pal_true s) v)
end YM.RG08.Halo
