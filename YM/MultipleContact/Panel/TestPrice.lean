import YM.MultipleContact.Panel.Slot

set_option autoImplicit false
set_option maxHeartbeats 1700000
noncomputable section
namespace YM.MultipleContact.Panel
open Set Function Filter MeasureTheory
open scoped ContDiff Classical BigOperators
def Cap {X:Type*}[NormedAddCommGroup X][NormedSpace ℝ X](k:ℕ)(f:X→ℂ)(A:ℝ) := 0 ≤ A ∧ ∀ x:X,∀i≤k, ‖iteratedFDeriv ℝ i f x‖ ≤ A
lemma blades_price {X:Type*}[NormedAddCommGroup X][NormedSpace ℝ X]{k:ℕ}{f:X→ℂ}{A:ℝ} (h:Cap k f A) (L:List X) (hd:L.length≤k)(hf:ContDiff ℝ ∞ f)(x:X): ‖blades L f x‖≤ A*(L.map (‖·‖)).prod:=by
       let m:=L.get; have hL:List.ofFn m=L:=List.ofFn_get L
       change ‖blades L f x‖ ≤ _
       calc _= ‖iteratedFDeriv ℝ L.length f x m‖:= by conv_lhs=> rw [← hL,blades_eval hf]
            _≤ A*∏ i,‖m i‖:= (ContinuousMultilinearMap.le_opNorm ..).trans (mul_le_mul_of_nonneg_right (h.2 x _ hd) (Finset.prod_nonneg (fun _ _=>norm_nonneg _)))
            _= _:= by rw [show L.map (‖·‖) = (List.ofFn (fun i:Fin L.length=> ‖m i‖)) by conv_lhs=>rw [← hL,List.map_ofFn];simp only [Function.comp_def],List.prod_ofFn]
variable {ι X:Type*}[NormedAddCommGroup X][NormedSpace ℝ X]
variable {V:ι→Type*}[∀i,NormedAddCommGroup (V i)][∀i,InnerProductSpace ℝ (V i)]
variable (p:∀i,Lens X (V i))(hz:∀i j,i≠j→∀u,(p i).read ((p j).put u)=0)(hw:∀i u,‖(p i).put u‖≤ ‖u‖)
def Factors (s:ℝ) (L:List (ι×ℕ))(f:X→ℂ):X→ℂ:=match L with |[]=>f | h::t=>(p h.1).trim s h.2 (Factors s t f)
lemma Factors_smooth (s:ℝ) (L:List (ι×ℕ)){f:X→ℂ}(hf:ContDiff ℝ ∞ f):ContDiff ℝ ∞ (Factors p s L f):=by
      induction L with
      |nil=>exact hf
      |cons h _ IH=>exact Lens.trim_smooth _ _ _ IH

def payment (L:List (ι×ℕ)):ℕ:= (L.map fun h=>h.2+1).sum
def gain (m:ℕ)(s:ℝ):ℝ:= (m+2:ℝ)*(1+s⁻¹)^(m+1)
def market (s:ℝ)(L:List (ι×ℕ))(x:X):ℝ:=match L with |[]=>1 | h::t=>(gain h.2 s * ‖(p h.1).read x‖^(h.2+1))*market s t x
lemma market_nonneg {s:ℝ}(hs:0<s)(x:X)(L:List (ι×ℕ)):0≤ market p s L x:=by
     induction L; case nil=> exact zero_le_one
     case cons h t IH=> exact mul_nonneg (mul_nonneg (by have : 0 ≤ s⁻¹:=inv_nonneg.mpr hs.le; unfold gain;positivity) (by positivity)) IH
include hz
lemma market_close (s:ℝ) (x:X)(L:List (ι×ℕ))(k:ι)(h:∀i∈L,i.1≠k) (t:V k):market p s L ((p k).lay x t)=market p s L x:=by
       induction L with
       |nil=>rfl
       |cons w y IH=>
            obtain ⟨h,h'⟩:=List.forall_mem_cons.mp h
            have he(x'): (p w.1).read ((p k).put x')=0:=hz _ k h x'
            have hx : (p w.1).read ((p k).lay x t)=(p w.1).read x:=by unfold Lens.lay; change (p w.1).read ((p k).put t+ (x-(p k).put ((p k).read x)))=_; simp only [map_add,map_sub,he,sub_zero,zero_add]
            rw [market, hx, IH h'];rfl
include hz hw
lemma budget (s:ℝ)(hs:0 < s)(L:List (ι×ℕ))(hl:(L.map Prod.fst).Nodup){f:X→ℂ} {D:ℕ}{A:ℝ}(hf:ContDiff ℝ ∞ f)(hA:Cap D f A)(T:List X) (ht:T.length+payment L ≤ D) (hHide:∀u∈T,∀k∈L,(p k.1).read u=0)(x:X): ‖blades T (Factors p s L f) x‖ ≤ (A*market p s L x) * (T.map (‖·‖)).prod:=by
       induction L generalizing x T with
       |nil=>change ‖blades T f x‖ ≤ A*1*_; rw [mul_one]; exact blades_price hA T (by simpa [payment] using ht) hf x
       |cons w L IH=>
          let i:=w.1; let m:=w.2
          have h0 : (L.map Prod.fst).Nodup:= (List.nodup_cons.mp hl).2
          have hi':∀k∈L,k.1≠i:=by rintro k hk h; exact (List.nodup_cons.mp hl).1 (by exact List.mem_map.mpr ⟨k,hk,h⟩)
          let g:=Factors p s L f; let t0:ℝ:=(T.map (‖·‖)).prod
          have hg:ContDiff ℝ ∞ g:=Factors_smooth p s L hf
          let φ:=(p i).slice x (blades T g)
          have h':∀u∈T,(p i).read u=0:=fun u hu=>hHide u hu w (List.mem_cons_self ..)
          let M:= market p s L x; have hp:0 ≤ M:= market_nonneg p hs x L
          have hC:JetBounds (m+1) φ (A*M*t0):=by
             refine ⟨mul_nonneg (mul_nonneg hA.1 hp) (List.prod_nonneg (fun r hr=>?_) : 0 ≤ (T.map (‖·‖)).prod),?_⟩ -- maybe syntax
             · obtain ⟨x,hx,rfl⟩:=List.mem_map.mp hr; exact norm_nonneg _
             intro y j hj; refine ContinuousMultilinearMap.opNorm_le_bound (mul_nonneg (mul_nonneg hA.1 hp) (List.prod_nonneg (fun r hr=>?_) : 0 ≤ t0)) (fun q=>?_)
             · obtain ⟨x,hx,rfl⟩:=List.mem_map.mp hr; exact norm_nonneg _
             let H:=List.ofFn (fun u:Fin j=>(p i).put (q u)); let U:=H++T
             have hD:U.length+payment L≤D:=by change _ + _ ≤ _; simp only [U,List.length_append,H,List.length_ofFn,payment]; rw [payment,List.map_cons,List.sum_cons] at ht; change j ≤ _ at hj; omega -- ht uses w.snd
             have he:=IH h0 U hD (by
                 intro d hd k hk; rcases List.mem_append.mp hd with hv|hv
                 · obtain ⟨l,hl⟩:= List.mem_ofFn.mp hv; rw [← hl]; exact hz _ i (hi' k hk) _
                 exact hHide d hv k (List.mem_cons.mpr (Or.inr hk))) ((p i).lay x y)
             change ‖blades U (Factors p s L f) _‖≤_ at he
             rw [market_close p hz s x L i hi' _] at he
             -- pay product directional costs using put contractive
             have hT:0≤t0:=List.prod_nonneg (by intro r hr; obtain ⟨x,_,rfl⟩:=List.mem_map.mp hr; positivity)
             have hcost:(U.map (‖·‖)).prod ≤ t0*∏k:Fin j, ‖q k‖:=by
                     unfold U; rw [List.map_append,List.prod_append,mul_comm]; apply mul_le_mul_of_nonneg_left _ hT
                     simp only [H,List.map_ofFn,List.prod_ofFn]; change ∏k:Fin j,‖(p i).put (q k)‖ ≤ _
                     exact Finset.prod_le_prod (fun _ _=>norm_nonneg _) (fun _ _=> hw _ _)
             calc ‖_‖= ‖blades U g ((p i).lay x y)‖:=by unfold φ; rw [(p i).slice_deriv j x (blades_smooth hg _),← blades_eval (blades_smooth hg _),blades_join]
                _ ≤ A*M*(U.map (‖·‖)).prod :=he
                _ ≤ A*M*(t0 * ∏ k,‖q k‖):=mul_le_mul_of_nonneg_left hcost (mul_nonneg hA.1 hp)
                _ = _:=by rw [← mul_assoc]
          change ‖blades T ((p i).trim s m g) x‖≤ (A* (gain m s * ‖(p i).read x‖^(m+1)*M))*t0
          rw [(p i).blades_trim T h' g hg (i:=m),(p i).trim_on s m (blades_smooth hg T)]
          unfold gain; exact (diff_bound hs ((p i).slice_smooth x (blades_smooth hg T)) m hC _).trans_eq (by ring)
end YM.MultipleContact.Panel
