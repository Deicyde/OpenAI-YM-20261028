import YM.RG08.Halo.Parcel
import YM.Next.STATIONARY.Lift.Pathways
/-! # Real colors through shifts and polynomial windows on the same stencil dictionary.
Transfer index is axis and real color. `Melt` at cover preimages WITHOUT replacing site
 parameters for output. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Halo
open Forms Function Finset Jetty Lattice Isles Pert.Bulk Stationary Spar Camera Glyph Filter Laurent RG Precision Exterior Skiff Trickle Weald Hatch Carrel Quarry
open Planned.PrimaryIntegral295 Place Carrier Flint Lagoon Yurt Next.Free
open scoped Classical ContDiff BigOperators Topology ENNReal
variable {G:Gauge}{I J:Type}{n m k p d:ℕ}{u D C B θ σ:ℝ}{L:Side}{K:Kernel I J}
local notation "A"=>Loc G 1

-- mask continuous iso. bound multiplicative
private def bef (G:Gauge):(Loc G 1→ℝ)≃ₗ[ℝ](Axis→G.Color) where
 toFun f a:= heavy G (fun i=>f (coord a,i))
 map_add' _ _:=by ext;rfl
 map_smul' _ _:=by ext;rfl
 invFun x i:=x (back i.1) i.2
 left_inv x:=by ext i; change x (coord (back i.1),i.2)=_;rw [show coord (back i.1)=i.1 from axisEquiv.apply_symm_apply i.1]
 right_inv x:=by ext i j;change x (back (coord i)) j=x i j;rw [back_axis]

def bonnet (G:Gauge):(Loc G 1→ℝ)≃L[ℝ](Axis→G.Color):=(bef G).toContinuousLinearEquiv
private def colorPn (b:G.ColorIndex):G.Color→L[ℝ] ℝ:=(ContinuousLinearMap.proj b).comp (heavy G).symm.toContinuousLinearMap

def relay (G:Gauge):Masked G→ (E4→Axis→G.Color):=fun x=>⇑(bonnet G) ∘ x
def depict (G:Gauge): (E4→Axis→G.Color)→Masked G:=fun x=>⇑(bonnet G).symm ∘ x
lemma depict_apply (x:E4→Axis→G.Color)(i:E4)(a:A):depict G x i a=x i (back a.1) a.2:=rfl
lemma relay_back (x:E4→Axis→G.Color):relay G (depict G x)=x:=by funext i;change bonnet G ((bonnet G).symm (x i))=_;rw [(bonnet G).apply_symm_apply]
lemma depict_back (x:Masked G):depict G (relay G x)= x:=by funext i;change (bonnet G).symm ((bonnet G) (x i))=_;rw [(bonnet G).symm_apply_apply]
lemma depict_add (x y:E4→Axis→G.Color):depict G (x+y)=depict G x+depict G y:=by ext;rfl
lemma depict_sub (x y:E4→Axis→G.Color):depict G (x-y)=depict G x-depict G y:=by ext;rfl
lemma depict_smul (x:E4→Axis→G.Color)(a:ℝ):depict G (a • x)=a • depict G x:=by ext;rfl

lemma Pool.stir {E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F](L:E→L[ℝ] F){x:E4→E}(h:Pool u n m x C):Pool u n m (⇑L ∘ x) (‖L‖*C):=by
 refine ⟨Place.linear_band L _ h.band,mul_nonneg (norm_nonneg _) h.nice,fun i=>?_⟩
 exact (L.le_opNorm (x i)).trans ((mul_le_mul_of_nonneg_left (h.shape i) (norm_nonneg _)).trans_eq (by ring))
lemma Chit.at {f:Masked G}(h:Chit G n f C):Pool 1 n 1 f C:= ⟨h.fit,h.live,fun i=>by simpa using h.pay i⟩
lemma cit {f:Masked G}(hu:0≤u)(hd:u≤1)(h:Pool u n 1 f C):Chit G n f (C*u):=by
 refine ⟨h.band,mul_nonneg h.nice hu,fun i=>(h.shape i).trans ?_⟩
 rw [pow_one];have he:=h.nice;gcongr;exact mul_le_of_le_one_left (norm_nonneg _) hd
-- identification of joint color stencil action on all polynomial directions through j. Polynomial cap so row absolute. Absolute `roll` exchange first with center/no γ.
lemma colony_new {x:Cover}:Carrier.cellar L x=Stationary.rent L x:=Stationary.rent_unique (Carrier.balance L x)
lemma ballet_read {M:Carrier.Lines L}(hM:Whole M)(f:Masked G)(hh:Chit G p f D)(he:Tutor L σ C M G 0)(hs:0<σ)(hc:0≤C)(o:Site L)(x:Ed G Cover):
 melt (Ballet G L M []) (Lattice.lift o) (Yurt.inlet f) x=(Carrier.applyLine M (Carrier.verdict (relay G f)) (x.1+Lattice.lift o) (back x.2.1)) x.2.2:=by
 let X:=x.1+Lattice.lift o; let a:=back x.2.1; let q:=x.2.2;let z:=Lattice.wrap L X;let v:=Stationary.rent L X
 let V:=Yurt.inlet f;let H:=Ballet G L M []
 have hv:Bearing (stance A) p 0 D V:= exhausted hh le_rfl le_rfl
 have ht:= row_budget (he [] (by simp)) hs (div_nonneg hc (by positivity)) hv o x
 let P:Cover× A→ℝ:=push H (Lattice.lift o) V x
 have hp:Summable P:=ht.1.of_norm
 unfold melt
 change ∑' y,P y = colorPn q (Carrier.applyLine M (Carrier.verdict (relay G f)) X a)
 have hN: (∑' y,P y)=∑ i:A,∑' (t:Cover),P (t,i):= by rw [hp.tsum_prod, ← hp.tsum_comm (f:=fun t:Cover=>fun i:A=>P (t,i)), tsum_fintype] -- hp f mismatch
 rw [hN,Fintype.sum_prod_type,Carrier.applyLine,map_sum,← Equiv.sum_comp axisEquiv]; apply sum_congr rfl; intro i _
 rw [sum_eq_single_of_mem q (mem_univ _)];swap
 · intro j _ hj
   unfold P push H Ballet install Spar.prism;simp [show x.2.2 ≠ j from Ne.symm hj]
 -- orientation i from axisEquiv : Axis ≃TypeFace. q coloring K. need comm map_tsum using absolute f coeff.
 unfold Carrier.stream
 let W(t:Cover):=Carrier.member M X a i t • (Carrier.verdict (relay G f)) (Carrier.cellar L X+t) i
 have hw:Summable W:=by
    obtain ⟨R,hR⟩:=Carrier.royalties p (relay G f) (Place.linear_band (bonnet G).toContinuousLinearMap _ hh.fit)
    -- row Whole strip not given! derive W via ∀ b finite from P some columns. need additional Whole M or price_eq via b identity all q. easiest require Whole.
    obtain ⟨s,payer,hs,H⟩:=hM
    exact (Carrier.stream_income hs (H (z,coord a) (coord i)) _ _ hR.1 (fun i'=>hR.2 i' _)).2.1.of_norm
 change _= colorPn q ( ∑' t,W t)
 rw [ContinuousLinearMap.map_tsum (colorPn q) hw]
 let e:=Equiv.addLeft v
 rw [←Equiv.tsum_eq e];apply tsum_congr;intro t
 unfold P push H W V Yurt.inlet
 unfold Ballet Spar.prism install;dsimp only;rw [if_pos rfl,map_smul]
 rw [colony_new]
 change M (wrap L X,x.2.1) (axisEquiv i) (v+t-rent L X) * f (Place.seat (v+t)) (axisEquiv i,q)=Carrier.member M X a i t* f (Place.seat (v+t)) (coord i,q)
 have hx:coord a=x.2.1:=axisEquiv.apply_symm_apply _
 rw [←hx]; change _ = M (wrap L X,coord a) (axisEquiv i) t*_
 unfold v;rw [add_sub_cancel_left];rfl
end YM.RG08.Halo
