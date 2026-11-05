import YM.RG08.Cast.Home

/-! # Signed group pinned K, any phase where Sworn incl admitted witness supplies -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Cast
open Lattice Laurent Forms Pert.Bulk Isles Packets Carrel Filter Finset Function RG
open Anchor Rudder Rudder.Symmetry Exterior Stationary Bloch RG08.Flat Spar Next.Free Rows Bid Precision
open scoped Topology ContDiff Classical BigOperators ENNReal Matrix
variable {G:Gauge} {B:Bed}{P:Side}{c:Clip}
local notation "o"=>(0:Fin 2)
local notation "u"=>(Fin.succ (0:Fin 1))

private def stone(b:Body 1 P)(i:G.ColorIndex):Cmix P G.ColorIndex 1:=(b.1,b.2,i)

lemma directors_signed (s:Signed)(v:Vert P (Rayk G 1)): pulled (directors G v) s=directors G (treated s v):=by
 ext ⟨x,b⟩ i
 obtain ⟨j,rfl⟩:=axisEquiv.surjective b
 have ht:=congrFun (tread s v) (x,j) -- cannot directly inject; use shift formula
 unfold directors treated pulled
 change ((let p := posDir (axisEquiv.symm (axisEquiv j)); let d:=p.rotate s; let e:=d.used (affine s 0 x); if d.neg then -heavy G (fun y=>v (e.1,coord e.2,y)) else heavy G (fun y=>v (e.1,coord e.2,y))):G.Color) i= supply s ((axisEquiv j),i)*v (badge s (x,(axisEquiv j),i))
 rw [axisEquiv.symm_apply_apply]
 rw [show axisEquiv j=coord j from rfl, passport,tariff]
 cases he:s.flip j <;>simp [Step.used,Step.rotate,posDir,he,affine,heavy,sub_eq_add_neg]

private lemma scroll (H:Bed)(v:Vert P (Rayk G 1)) : reading (arcade (quadratic H P)) v=gaugeFiscal H (directors G v) (directors G v):=by
 let f(_k:Fin 2):=Co P (Kind G.ColorIndex 1)
 unfold Carrel.reading
 rw [← (Fin.consEquiv f).sum_comp _,Fintype.sum_prod_type]; simp_rw [Fin.prod_univ_two]
 unfold gaugeFiscal Matrix.mulVec directors; simp_rw [dotProduct,Finset.mul_sum]
 let M:=Precision.K (H.metric.acts P)
 have he {F : f o→ℝ}: (∑ z,F z)=(∑ j:G.ColorIndex,∑ b:Body 1 P,F (b.1,b.2,j)):=by
    let e: G.ColorIndex×Body 1 P≃f o:=(Equiv.prodComm ..).trans (Equiv.prodAssoc ..)
    rw [←e.sum_comp, Fintype.sum_prod_type];rfl
 have ht {F:(Fin 1→f o)→ℝ}: (∑ z,F z)=∑ x:f o,F (fun _=>x):=by
    rw [← (Equiv.funUnique (Fin 1) (f o)).symm.sum_comp];rfl
 change (∑ x:f o,∑ y:Fin 1→f o,arcade (G:=G) M (Fin.cons x y)*(v x*v (y 0)))=∑ j:G.ColorIndex,∑ b:Body 1 P,∑ m:Body 1 P,v (b.1,b.2,j)*(M b m*v (m.1,m.2,j))
 rw [he];iterate 2 (apply Finset.sum_congr rfl;intro i h)
 rw [ht,he] -- simp recursion
 unfold arcade Spar.shaded
 simp only [Fin.cons_zero,Fin.cons_succ,Matrix.of_apply,ite_mul,zero_mul,Prod.mk.eta,Finset.sum_ite_irrel,Finset.sum_const_zero,sum_ite_eq,if_pos (mem_univ _)]
 apply Finset.sum_congr rfl;intro a _; ring

lemma oath (G:Gauge){σ C τ Q:ℝ}(h:B.metric.strip σ C)(hf:∀ P,Floor B c P τ Q)(hs:0<σ)(hC:0≤C)(_ht:σ≤1)(hk:∀ P,Sworn B P G):
 Cardinal (picture G.ColorIndex 2 (beam G (plain B.metric))):=by
 let F:=beam G (plain B.metric);let Y:=picture G.ColorIndex 2 F
 have he: NextTo F σ (tax G 2*C):= NextTo.unit hs (by unfold tax; positivity) (Anchor.expand_path (spur_path (pass_one _))) (Anchor.expand_cost (spur_cost (plain0 h le_rfl).1 (plain0 h le_rfl).2 hC hs.le)) (by decide)
 have hp:Held (carpet (Tone G.ColorIndex)) (σ/2) (flashes G.ColorIndex 2 σ*(tax G 2*C)) Y:= encode (by decide) hs (by unfold tax; positivity) he.cohort (Anchor.expand_cost (spur_cost (plain0 h le_rfl).1 (plain0 h le_rfl).2 hC hs.le))
 have hh:= (photograph he).cohort
 have hD:= dressed_symm (G:=G) (N:=chain) (M:=fun P=>B.metric.acts (chain P)) (show Tendsto (fun i=>(chain i).val) atTop atTop by rw [tendsto_atTop_atTop];intro b; exact ⟨b,fun i hi=>by dsimp [chain];omega⟩) (fun j=>matches_plain _) (fun j=>(hf _).symmetric.1) (pass_one _) (plain0 h le_rfl).1 hs hC
 have hc:Sym Y:=fun i=>by unfold Y;rw [←picture_woven,hD i]
 intro s; change orbit s Y=Y
 apply compress_inj (k:=1) _ _ (orbit_graded (s:=s) (bearing (F:=F) expand_grade).2) (bearing (F:=F) expand_grade).2
 rw [←adjust_compress]
 apply crystals (σ:=σ/2) (τ:=σ/2) o (by positivity) (by positivity) (adjust_cohort (compress_path _ hh) s) (compress_path _ hh) _ (compress_sym _ hc) (adjust_cost (compress_cost _ hp) (by positivity) _) (compress_cost _ hp)
 · intro P _ z
   have hv:=according s⁻¹ (compress_path 1 hh) (P:=P) o z
   rw [inv_inv] at hv;rw [hv];unfold F;rw [picture_arcade (matches_plain _) he, ← show Flat.quadratic B P=Precision.K (B.metric.acts P) from rfl,scroll B,scroll B,← directors_signed,hk]
 have hw (i:Equiv.Perm (Fin 2)):woven (orbit s Y) i=orbit s (woven Y i) := by
    ext x;unfold woven;rw [orbit_apply,orbit_apply];congr 1;exact Equiv.prod_comp i (fun j=>toll s (x j).2.1)
 rw [adjust_compress];exact compress_sym _ (fun i=>by rw [hw,hc i])
end YM.RG08.Cast
