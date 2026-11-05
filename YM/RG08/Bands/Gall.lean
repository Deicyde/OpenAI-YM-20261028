import YM.RG08.Bands.Vernal
/-!
# Native coupling at each step is exact substitution through polynomial product.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.RG08.Bands
open Filter Analysis Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Reflect Work.F08 Push.AbsoluteSums Matrix
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Summit Scores Door Run Staffer PertExtension.Series PertExtension.Series.Radial PertExtension.Series.Tested Town PowerSeries
open scoped BigOperators Topology Real ContDiff Classical Matrix.Norms.Frobenius
variable {I α :Type} [Fintype α]{u:List I}{a:I→ℕ}{F V:Screed ℝ α}{S:Canticle α}{U:I→ Screed ℝ α}{K:Row α α}{p:Option Side}{t k n e τ r s:ℕ}{m c:Side}
section hill
def atlasB (V:Screed ℝ α)(r:ℕ)(o:Site c)(v:PAC α c) : PowerSeries ℝ:= PowerSeries.mk fun i=> rootSong (V i r) c o v
lemma braid_bullet (h: Sails k F)(hp:Sails t V)(o:Site c)(v:PAC α c)(r:ℕ): atlasB (gust F V) r o v=∑ p∈wheel r,atlasB F p.1 o v * atlasB V p.2 o v:= by
   ext i; unfold atlasB; rw [coeff_mk,_root_.map_sum]; unfold gust; rw [Finset.sum_apply,root_sum o (wheel i) (h:=fun b _=> (braid_loom (h.thin b.1) (hp.thin b.2)).tide r|>.pens)] -- wrong tide of input product! correct
   rw [Finset.sum_apply]; unfold spoolB; simp_rw [fun j k=>root_sum (i:=o) (f:=fun v=>(grant r (braidV (F j v.1) (V k v.2)))) (wheel r) (h:=fun w _=> (Tidied r (braid_tid (h.tide j w.1|>.pens) (hp.tide k w.2|>.pens))).pens)]
   simp only [Finset.sum_apply]; rw [sum_comm]; refine sum_congr rfl fun j hj=>?_ ; rw [coeff_mul]; refine sum_congr rfl fun i hi=>?_ ; rw [← mem_antidiagonal.mp hj,grant_self, join_song (h.tide i.1 _|>.pens) (hp.tide i.2 _|>.pens),coeff_mk,coeff_mk]; rfl
lemma hill_cast (h:Sails k F)(ψ:PowerSeries ℝ): Sails k (Tall.hill ψ F):= let a:=hill_rank ψ h.budget h.tide; ⟨a.2,a.1⟩
lemma spectra (h:Sails k F)(o:Site c)(v:PAC α c)(ψ:PowerSeries ℝ)(r:ℕ): atlasB (Tall.hill ψ F) r o v= (ψ⁻¹)^r*PowerSeries.subst (PowerSeries.X*ψ) (atlasB F r o v):= by
   ext i; unfold atlasB; rw [coeff_mk, glaze_orient]; unfold Tall.hill
   rw [root_sum o (range _) (h:=fun b _=>(h.tide b r).pens.scale _),Finset.sum_apply]; exact sum_congr rfl fun j _=> congr_fun (root_scale o (h.tide j _|>.pens) _) _
lemma spectrum_b (h:Sails k F)(hp:Sails t V)(ψ:PowerSeries ℝ): Tall.hill ψ (gust F V)= gust (Tall.hill ψ F) (Tall.hill ψ V):= by
   let A:= PowerSeries.X*ψ; let Q: PowerSeries ℝ→ₐ[ℝ] PowerSeries ℝ:= PowerSeries.substAlgHom (a:=A) (.of_constantCoeff_zero' (by unfold A; simp)); have hQ: (Q:PowerSeries ℝ→PowerSeries ℝ)=PowerSeries.subst A:=coe_substAlgHom _
   let H:=Tall.hill ψ F; let K:=Tall.hill ψ V; let P:= Tall.hill ψ (gust F V)
   have hv o r (z:Site o)(v:PAC α o): atlasB P r z v=atlasB (gust H K) r z v:= by
       unfold P H K; rw [spectra (braid_s h hp),braid_bullet (hill_cast h ψ) (hill_cast hp ψ),braid_bullet h hp z v, ←hQ]; rw [_root_.map_sum,Finset.mul_sum]; refine sum_congr rfl ?_; intro p hp'; rw [spectra h, spectra hp,show r=p.1+p.2 from (mem_antidiagonal.mp hp').symm, pow_add,_root_.map_mul]; rw [show Q _ = _ from congr_fun hQ (atlasB F p.1 z v),show Q _=_ from congr_fun hQ (atlasB V p.2 z v)]; ring
   funext i r; refine Tidy.uniquely ((hill_cast (braid_s h hp) _).tide _ _) ((braid_s (hill_cast h _) (hill_cast hp _)).tide _ _) fun m=>funext fun v=>?_ ; have hx:= congr_arg (PowerSeries.coeff i) (hv m r 0 v); unfold atlasB at hx; simp_rw [coeff_mk] at hx; exact hx
lemma growth_unit (ψ:PowerSeries ℝ): Tall.hill ψ (spine_one α)=spine_one α:= by
   funext i r; unfold Tall.hill; by_cases hr:r=0
   · subst r; rw [sum_eq_single_of_mem 0 (mem_range_succ_iff.mpr (Nat.zero_le _))]; swap; · intro i _ hi; rw [spine_one,if_neg (by omega),smul_zero]
     unfold glaze spine_one; simp only [pow_zero,mul_one,sub_zero, if_pos rfl, add_zero, PowerSeries.coeff_one]; split <;> simp_all
   refine Eq.trans (sum_eq_zero fun j _=>?_) ?_ <;> simp [spine_one,hr,add_eq_zero]
lemma spectra_cast (h:∀ i∈u,Sails (a i) (U i))(ψ:PowerSeries ℝ): Tall.hill ψ (castF U u)= castF (fun i=> Tall.hill ψ (U i)) u := by
   induction u with
   | nil=> exact growth_unit _
   | cons i u ih=>
     have hp j hj:= h j (List.mem_cons_of_mem (l:=u) _ hj); change Tall.hill _ (gust (U i) (castF U u))=gust _ (castF _ u)
     rw [spectrum_b (h i List.mem_cons_self) (cast_s hp), ih hp]
end hill
section springs
variable {G:Gauge}{U F : Tale G}{L:Side}
lemma sails_k (p:Site L)(h:Sails k U): Sails k (reachP p U):= let a:= reaches h.budget h.tide p; ⟨a.2,a.1⟩
lemma gust_springs (p:Site L)(h:Sails k U)(hp:Sails t F): reachP p (gust U F)=gust (reachP p U) (reachP p F) := by
   apply unrolled (sails_k p (braid_s h hp)) (braid_s (sails_k p h) (sails_k p hp)); intro i m; let g: Ratio m (m*L):=⟨L,rfl⟩; let z:= g.assemble (0,p)
   have he (U:Tale G) n (h:Sails n U) k (x:PAC (Park G L) m): large (0:Site m) (n+k) (reachP p U k) x= large z (n+k) (U k) (fineL G g x):= by unfold large; rw [Finset.sum_apply,Finset.sum_apply]; exact sum_congr rfl fun j _=> lot_period g p (h.tide k j|>.pens) x 0
   funext x; rw [he _ _ (braid_s h hp),sing_k h hp, sing_k (sails_k p h) (sails_k p hp)]; unfold billow; rw [Finset.sum_apply,Finset.sum_apply]; exact sum_congr rfl fun j hb=> (congr_arg₂ (·*·) (he U k h j.1 x) (he F t hp j.2 x)).symm
lemma stem0 (p:Site L): reachP p (spine_one (Loc G 1))=spine_one (Park G L):= by
   apply unrolled (sails_k p sails_start) sails_start; intro i m; rcases i with _|i
   · funext x; let g: Ratio m (m*L):=⟨L,rfl⟩; unfold large; simp only [add_zero,zero_add,range_one,sum_singleton]; unfold reachP; rw [lot_period g p (sails_start.tide 0 0|>.pens)]
     let v(m:Side):=spine_one (Park G L) 0 0
     have hp : ∀ (α:Type)[Fintype α]{m: Side}(z:Site m) (y:PAC α m),rootSong (spine_one α 0 0) m z y=1:= by intro α _ m z y; unfold rootSong Tensor.diagonal; rw [stitch_apply (sails_start.tide 0 0|>.pens.of_norm)]; simp [rosary,spine_one]
     rw [hp, hp]
   unfold large reachP spine_one; simp

variable {V:I→ Tale G}
lemma reach_full (p:Site L)(h:∀ i∈u,Sails (a i) (V i)): reachP p (castF V u)=castF (fun i=>reachP p (V i)) u:= by
   induction u with
   | nil=> exact stem0 p
   | cons i u ih=>
     have hp j hj:= h j (List.mem_cons_of_mem (l:=u) _ hj); change reachP p (gust (V i) (castF V u))= gust _ (castF _ u); rw [gust_springs p (h i List.mem_cons_self) (cast_s hp),ih hp]
end springs
end YM.RG08.Bands
