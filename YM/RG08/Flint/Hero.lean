import YM.RG08.Flint.Hunger

/-! # Scaled charge per slot, multi-linear exact.
- single gradient & replacement variants in same lemma.
- admissible δ can be maximum before L. record derivative scaling separate.
- interference of gauges only lower order tickets.
-/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Flint
open Forms Function Finset Jetty Lattice Isles Pert.Bulk Skiff Trickle
open Room Gallery Camera MvPolynomial Glyph Quarry Weald Hatch Carrel Laurent Filter Stationary
open scoped Classical ContDiff BigOperators Topology PowerSeries ENNReal
variable {I J:Type}{G:Gauge}{n l p e d:ℕ}{C δ a σ B:ℝ}{w:G.El}{h:0<σ}
private lemma shrink {X:I→ℝ}{L:Jetty.Loom I}(h:Bearing L p δ a X)(ha:a≠0): Bearing L p δ 1 (a⁻¹ • X):=by
 have hv := h.smul a⁻¹; rwa [abs_of_nonneg (inv_nonneg.mpr h.1),inv_mul_cancel₀ ha] at hv
lemma Bearing.dry {L:Jetty.Loom I}{X:I→ℝ}(h:Bearing L p δ 0 X):X=0:=funext fun i=>abs_eq_zero.mp (le_antisymm (by simpa using h.2 i) (abs_nonneg _))
lemma Bearing.here {L:Jetty.Loom I}{X:I→ℝ}(h:Bearing L p δ a X){τ:ℝ}(ht:δ≤τ){k:ℕ}(hk:p≤k):Bearing L k τ a X:=by
 refine ⟨h.1,fun i=>(h.2 i).trans (mul_le_mul_of_nonneg_left ?_ h.1)⟩
 unfold hustle; have hx:=L.nn i;gcongr; linarith
/-- preweight restoration & single ∇ insertion. Quantitative cost even if A_tr prices post.
 Applies before summing y(capture whole list factor ∏ K) and BEFORE L by using δ_f announced
 and disabling budgets under decreasing δ. At h common. -/
theorem spark_band (G:Gauge)(l e n p:ℕ)(σ δ:ℝ)(hσ:0<σ)(hδ:0≤δ)(hδ':δ≤1)(hz:(↑((e+1)*(l+e)):ℝ)*δ≤σ/2)(hR:n≤l+e):∃ D:ℝ,0≤D ∧ ∀ (X:Fin n→Ed G Cover→ℝ)(U:Fin n→Nd G Cover→ℝ)(K:Fin n→ℝ),
 (∀ i,Bearing (stance (Loc G 1)) p δ (K i) (X i))→(∀ i,Bearing (stance G.ColorIndex) p δ (K i) (U i))→ ∀ (M:GrainS (Ed G Cover))(d:ℕ)(B T:ℝ)(f:Pearl),Calls l M → Permit d l M → 0≤B→0≤T→(∀ i<e,∀ k≤l+i,Sings (stance _) d hσ (M i k) B)→(∀ k≤l+e,Sings (stance _) d hσ (M e k) T)→
 let C := D*(∏ i,K i)*B*beam d hσ f
 ; |sonic (M e n) f (fun i=>X i+grad (U i))-sonic (M e n) f X|≤C ∧ ∀ k:Fin n,|sonic (M e n) f (Function.update X k (grad (U k)))|≤C:=by
 obtain ⟨D,hD,H⟩:=spark G l e n p σ δ hσ hδ hδ' hz hR
 refine ⟨D,hD,fun X U K hX hU M d B T f he h hB hT hM hE=>?_⟩
 have hK(i):0≤K i:=(hX i).1
 let C:=D* (∏ i,K i)*B*beam d hσ f; have hC:0≤C:=by unfold C; have hx:=prod_nonneg (s:=Finset.univ) (f:=K) (fun i _=>hK i);have hh:=beam_nn d hσ f; positivity
 let L:=M e n
 have hh{x:Fin n→Ed G Cover→ℝ}{u:Fin n→Nd G Cover→ℝ}(hx:∀ i,Bearing (stance _) p δ (K i) (x i))(hu:∀ i,Bearing (stance _) p δ (K i) (u i)):
       |sonic L f (fun i=>x i+grad (u i))-sonic L f x|≤C:=by
    by_cases Hq:∃ i,K i=0
    · obtain ⟨k,hk⟩:=Hq;have hv:x k=0:=(hk ▸ hx k:Bearing (stance _) p δ 0 (x k)).dry; have Ht:u k=0:=(hk ▸ hu k:Bearing (stance _) p δ 0 (u k)).dry
      have hr:x k+grad (u k)=0:=by rw [hv,Ht,show grad (G:=G) 0=0 from by funext _; simp [grad],add_zero]
      change |sonic _ _ _-sonic _ _ _|≤C
      rw [sonic_zero (F:=L) hv f,sonic_zero (F:=L) (X:=fun i=>x i+grad (u i)) (i:=k) hr f,sub_zero,abs_zero];exact hC
    push Not at Hq
    let y(i:Fin n):=(K i)⁻¹ • x i; let v(i:Fin n):=(K i)⁻¹ • u i
    have H:=H y v (fun i=>shrink (hx _) (Hq i)) (fun i=>shrink (hu _) (Hq i)) M d B T f he h hB hT hM hE
    have hp: x=(fun i=>K i • y i):=by funext i;unfold y; rw [smul_smul,mul_inv_cancel₀ (Hq i),one_smul]
    have hg: u=(fun i=>K i • v i):=by funext i;unfold v; rw [smul_smul,mul_inv_cancel₀ (Hq i),one_smul]
    rw [hp,hg,show (fun i:Fin n=>K i • y i+grad (K i • v i))=(fun i:Fin n=>K i • (y i+grad (v i))) from by funext i s;simp only [grad,Pi.add_apply,Pi.smul_apply,smul_eq_mul];ring,sonic_pull,sonic_pull,← mul_sub,abs_mul,abs_of_nonneg (prod_nonneg (fun i (_:i∈(Finset.univ:Finset (Fin n)))=>hK i))]
    refine (mul_le_mul_of_nonneg_left H (prod_nonneg fun i (_:i∈(Finset.univ:Finset (Fin n)))=>hK i)).trans_eq (by unfold C; ring)
 refine ⟨hh hX hU,fun k=>?_⟩
 let x:=Function.update X k 0; let u:Fin n→Nd G Cover→ℝ:=Pi.single k (U k)
 have hy(i):Bearing (stance _) p δ (K i) (x i):=by unfold x; by_cases he:i=k;subst k; simpa using Bearing.nil.up (hK i); simpa [he] using hX i
 have hr(i):Bearing (stance _) p δ (K i) (u i):=by unfold u; by_cases he:i=k;subst k; simpa using hU i; simpa [he] using Bearing.nil.up (hK i)
 have hv:=hh hy hr
 rw [sonic_zero (F:=L) (i:=k) (Function.update_self ..) f,sub_zero] at hv
 have ht:(fun i=>x i+grad (u i))=Function.update X k (grad (U k)):=by funext i t; by_cases he:i=k <;> simp [he,x,u,grad]
 rw [ht] at hv;exact hv
end YM.RG08.Flint
