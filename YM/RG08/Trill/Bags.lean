import YM.RG08.Trill.Dean
/-! # Single projection unit. Bounded both directions, spanning and leading properties.
For ker on WHOLE Stencil recipe or higher mesh-compare; at any rooted pre-origin width. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Trill
open Forms Function Finset Jetty Lattice Isles Pert.Bulk Skiff Trickle
open Room Gallery Camera MvPolynomial Glyph Quarry Weald Hatch Carrel Laurent Filter Stationary Flint
open Planned.PrimaryIntegral295 Place Film Labels Source Source.Drops WardBin Parts
open scoped Classical ContDiff BigOperators Topology ENNReal ComplexConjugate Matrix.Norms.Frobenius
variable {G:Gauge}{d n p l e D k:ℕ}{σ B:ℝ}
local notation "E"=>Ed G Cover
local notation "Y"=>Snap G d
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 600000
private lemma grant_wedge (G:Gauge)(d n p:ℕ)(σ:ℝ)(hs:0<σ): ∃ W:Snap G d→ℝ,∀ D:ℕ,∀ (F:Gras G n)(B:ℝ),Lyrics F→ Sings (stance _) D hs F B→ 0≤B→∀ (f:Pearl)(z:Snap G d),|grants F f p d z|≤ W z * (B * beam D hs f):=by
 choose C hC H using key_budget G d
 let u(a:Fin n→Fin (p+1))(z:Snap G d)(j:Fin n):=C (a j).val*∏ _i:Fin (a j).val,‖z‖
 let s:Finset (Fin n→Fin (p+1)):=Finset.filter (fun a=>∑ i,(a i).val=p) univ
 refine ⟨fun z=>s.sum fun a=>tribute (d*p) σ (u a z),fun D F B hF hP hB f z=>?_⟩
 unfold grants;rw [sum_mul];apply (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _=>?_)
 rw [←mul_assoc];exact sonic_le hF hP hB f (le_rfl:(0:ℝ)≤0) (by rw [mul_zero];exact (half_pos hs).le) (fun j=>(H (i j).val (fun _=>z)).here le_rfl (Nat.mul_le_mul_left _ (Nat.le_of_lt_succ (i j).isLt)))
/-- Universal coefficient read (uses R left Inverse extension off-space before establishing
 global rotation). U and all currencies BEFORE L. Horizon jacobi factor for test d.
-/
lemma grant_price (G:Gauge)(d n p k:ℕ)(σ:ℝ)(hs:0<σ)(U:Labels.Frame G d)(i:U.Index): ∃ C:ℝ,0≤C∧ ∀ D:ℕ,∀ (F:Gras G n)(B:ℝ),Lyrics F→ Sings (stance _) D hs F B→ 0≤B→∀ f:Pearl, |tally U p k i (harrow F f p d)| ≤ C * B * beam D hs f:=by
 obtain ⟨W,H⟩:=grant_wedge G d n p σ hs
 obtain ⟨C,hC,h⟩:=disc (tally U p k i) W
 refine ⟨C,hC,fun D F B he ha hB f=>?_⟩;rw [mul_assoc];apply h _ _ (mul_nonneg hB (beam_nn ..)) (harrow_sym he ha hB _)
 intro z;rw [harrow_diag he ha hB];exact H D F B he ha hB f z

-- analytic diagonal value linearized at rank n, admits polarization over whole kernel. Need mixed.
lemma pluck_combine (z:Fin p→Y)(s:Fin p→ℝ) : pluck 1 (∑ i,s i • z i)=∑ i:Fin p,s i • pluck 1 (z i):=by
 funext j
 let M:=@keytar G d j 1
 let F:=M.curryLeft
 rw [Finset.sum_apply];change M (fun _:Fin 1=> _)= ∑ i:Fin p,s i*M (fun _=> z i)
 have h(x:Y):M (fun _=>x)=F x (0:Fin 0→Y):=congrArg M (show (fun _:Fin 1=>x) = Fin.cons x (0:Fin 0→Y) from funext fun i=>by have he:i=0:=Subsingleton.elim _ _;simp [he])
 simp_rw [h,map_sum,_root_.sum_apply,_root_.map_smul,_root_.smul_apply,smul_eq_mul]
variable {F:Gras G n}{g:0<σ}
lemma grants_chord (he:Lyrics F)(hh:Sings (stance _) D g F B)(hb:0≤B)(f:Pearl)(hc:Forms.Sym (fun x=>F x f))(z:Fin n→Y) :
 harrow F f n d z=sonic F f (pluck 1 ∘ z):=by
 let M:=harrow F f n d;let Q:Flake n (Fin n):=fun t=>M (z ∘ t)
 let Q':=modal F f (pluck 1 ∘ z)
 have ho:=harrow_sym (p:=n) (d:=d) he hh hb f
 suffices Q=Q' from congrFun this id
 apply Carrel.pursuit (F:=Q) (V:=Q') (fun w=>funext (fun t=>ho (z ∘ t) w)) (modal_sym f hc)
 apply MvPolynomial.funext;intro u
 let K(j:Fin n):E→ℝ:=pluck 1 (z j)
 obtain ⟨C,_,H⟩:= key_budget G d 1
 change (MvPolynomial.eval u (parley Q))=(MvPolynomial.eval u) (parley (modal F f K))
 rw [←modal_read (X:=K) f he hh hb u (fun j=>C * ∏ _i:Fin 1,‖z j‖) (le_rfl:(0:ℝ)≤0) (by rw [mul_zero];exact (half_pos g).le) (fun j=>H (fun _=>z j)),show (∑ i:Fin n,u i • K i)=pluck 1 (∑ i:Fin n,u i • z i) from (pluck_combine z u).symm,← grants_edge F f, ←harrow_diag he hh hb, parley_street]
 unfold Tensor.diagonal;change _= M (fun _=>∑ i:Fin n,u i • z i)
 rw [M.map_sum (fun _ i=>u i • z i)];apply sum_congr rfl;intro i _; rw [M.map_smul_univ,mul_comm];rfl
