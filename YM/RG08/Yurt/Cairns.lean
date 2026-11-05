import YM.RG08.Yurt.Racks
import YM.RG08.Lagoon.Pen
import YM.RG08.Lagoon.Hull

/-! # Deterministic cancellation accounting. Use test dual `Lagoon` power, jointly,
 not a triangle inequality row-by-row without projection. in each column y.
-/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Yurt
open Forms Function Finset Jetty Lattice Isles Pert.Bulk Stationary Spar Camera MvPolynomial Glyph Quarry Weald Hatch Carrel Laurent Filter RG Precision Exterior Skiff
open Planned.PrimaryIntegral295 Place Carrier Flint Lagoon
open scoped Classical ContDiff BigOperators Topology ENNReal
variable {I:Type}{G:Gauge}{n p d e i:ℕ}{D C τ s δ:ℝ}{L:Side}
local notation "A" => Loc G 1
abbrev Masked (G:Gauge):=E4→(Loc G 1→ℝ)
structure Chit (G:Gauge)(i:ℕ)(f:Masked G)(D:ℝ):Prop where
 fit : f∈ Place.rangeLt (Loc G 1→ℝ) i
 live : 0≤D
 pay : ∀ x:E4, ‖f x‖≤D*(1+‖x‖)^i
lemma Chit.up {f:Masked G}(h:Chit G i f C)(hz:C≤D):Chit G i f D:=⟨h.fit,h.live.trans hz,fun x=> (h.pay x).trans (mul_le_mul_of_nonneg_right hz (pow_nonneg (by positivity) _))⟩
def inlet (f:Masked G)(i:Ed G Cover):ℝ:= f (Place.seat i.1) i.2
lemma exhausted {V:Masked G}(h:Chit G i V D)(he:i≤p)(hx:0≤δ): Bearing (stance A) p δ D (Yurt.inlet V):=by
 refine ⟨h.live,fun j=>?_⟩
 unfold Yurt.inlet;rw [←Real.norm_eq_abs]; apply ((norm_le_pi_norm _ j.2).trans (h.pay (Place.seat j.1))).trans (mul_le_mul_of_nonneg_left _ h.live)
 have hv:=Carrier.shade_seat j.1
 have hp:0≤length j.1:=abroad_nn j
 change _ ≤ (1+length j.1)^p * Real.exp _
 apply ((pow_le_pow_left₀ (by positivity) (show 1+‖Place.seat j.1‖≤1+length j.1 from by gcongr) _).trans (pow_le_pow_right₀ (le_add_of_nonneg_right hp) he)).trans
 exact le_mul_of_one_le_right (pow_nonneg (by linarith only [hp]) _) (Real.one_le_exp (mul_nonneg hx hp))
/-- geometric decomposition index (Trellis.neg stubs allowed). Test separately afterwards.
 last Fin carries pure remainder at grade h+1. -/
local notation "Lm" => Carrier.Lines L
variable (M:Lm)
def posed (h:ℕ)(o:Site L)(M:Lm)(τ:ℝ)(y:Market A)(i:Fin (h+1)):Ed G Cover→ℝ:=fun x=> if i.val<h then Yurt.inlet (newton G τ o M y i.val) x else Trellis.surplus (auction G τ o M y []) h x.1 x.2
def full (G:Gauge)(o:Site L)(M:Lm)(τ:ℝ)(y:Market (Loc G 1)):Ed G Cover→ℝ:=fun x=> auction G τ o M y [] x.1 x.2
lemma offer_read (m : Carrier.Lines L)(g:ℕ)(o:Site L)(y:Market A):full G o m τ y=∑ t:Fin (g+1),posed g o m τ y t:=by
 funext x;unfold full posed;rw [Fin.sum_univ_castSucc]
 rw [Pi.add_apply,Finset.sum_apply]
 simp only [Fin.val_last,lt_self_iff_false, if_false,Fin.val_castSucc,Fin.is_lt,ite_true]
 unfold Trellis.surplus Trellis.fitting;rw [Pi.sub_apply,Pi.sub_apply,Finset.sum_apply]
 unfold Yurt.inlet newton
 rw [Fin.sum_univ_eq_sum_range (fun i=> Trellis.sector i (auction G τ o m y []) (Place.seat x.1) x.2) g];ring

/-- Uniform announcement B before L. `2τ` convention left for caller. Use fixed δ. -/
lemma quarry (G:Gauge)(n:ℕ)(s C:ℝ)(ht:0≤ s)(hc:0≤C):∃ B:ℝ,0≤B∧∀ (L:Side){τ δ:ℝ}(o:Site L)(M:Carrier.Lines L),Odd L.val→0≤τ→τ≤ s → τ/(L.val:ℝ)≤δ → Tutor L s C M G n → ∀ (i:Fin (n+1))(y:Market (Loc G 1)),
 let u:=unitStep L
 ; Bearing (stance (Loc G 1)) n δ (B*u^(i.val+1)) (posed n o M τ y i) ∧ ( i.val<n → Chit G (i.val+1) (newton G τ o M y i.val) (B*u^(i.val+1))) :=by
 choose D hD H using fun i=>newton_price G s C hc ht i
 let Q:=∑ i:Fin (n+1),D i.val;have hq:0≤Q:=sum_nonneg fun _ _=>hD _
 let V:=C*Real.exp (4*s);have hv:0≤V:=mul_nonneg hc (Real.exp_pos _).le
 let B:=V+Q;have hb:0≤B:=add_nonneg hv hq
 refine ⟨B,hb,?_⟩; intro L τ δ o M hL hp hτ hδ hw i y u
 have hδ':0≤δ:=(div_nonneg hp (Nat.cast_nonneg _)).trans hδ
 have hu:0≤u:=(unitStep_pos L).le
 unfold posed; split_ifs with he
 · obtain ⟨hf,hG⟩:=H i.val L o M hL hp hτ (fun w hw'=>hw w (hw'.trans he.le)) y
   let f:=newton G τ o M y i.val
   have htF:Chit G (i.val+1) f (B*u^(i.val+1)):=by
      refine ⟨hf,mul_nonneg hb (pow_nonneg hu _),fun x=>?_⟩
      have hc':D i.val≤B:=(single_le_sum (s:=Finset.univ) (f:=fun i:Fin (n+1)=>D i.val) (fun i _=>hD _) (mem_univ i)).trans (le_add_of_nonneg_left hv)
      exact (hG x).trans (mul_le_mul (mul_le_mul_of_nonneg_right hc' (pow_nonneg hu _)) (pow_le_pow_right₀ (le_add_of_nonneg_right (norm_nonneg _)) (by omega : i.val ≤ i.val+1)) (pow_nonneg (by positivity) _) (mul_nonneg hb (pow_nonneg hu _)))
   exact ⟨exhausted htF he hδ',fun _=>htF⟩
 have hz:i.val=n:=by omega
 refine ⟨⟨mul_nonneg hb (pow_nonneg hu _),fun x=>?_⟩,fun H=>False.elim (he H)⟩
 rw [hz]; change |Trellis.surplus (auction G τ o M y []) n x.1 x.2| ≤ _
 rw [← Real.norm_eq_abs]; refine ((norm_le_pi_norm _ x.2).trans (remainder hL hp hτ hc hw o y x.1)).trans ?_
 unfold hustle; change V*u^(n+1)*(1+length x.1)^n*Real.exp ((τ/(L.val:ℝ))*length x.1)≤_*( (1+length x.1)^n*Real.exp (δ*length x.1))
 rw [←mul_assoc]; gcongr;exact le_add_of_nonneg_right hq
-- Null property on addressed polynomial inputs, before and after deformation.
def Minored (G:Gauge)(h n:ℕ)(M:Pack n (Ed G Cover))(B:ℝ):Prop:=∀ (u:Fin n→ℕ)(t:ℕ)(k:Cargo t)(f:Fin n→Masked G)(D:Fin n→ℝ),(t+∑ i,u i) ≤h→(∀ i,1≤u i)→ (∀ i,Chit G (u i) (f i) (D i)) → |sonic M (Lagoon.pal k) (Yurt.inlet ∘ f)| ≤ (∏ i:Fin n,D i)*B
-- `t+∑ i,...` parses fine? closed.
end YM.RG08.Yurt
