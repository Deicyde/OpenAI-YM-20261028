import YM.RG08.Halo.Spiral

/-! # Minored projection currency with exact diag.
Abs price equipment for polynomial purchases. Distinguish pre-scale tolerance & admitted h. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Halo
open Forms Function Finset Jetty Lattice Isles Pert.Bulk Stationary Spar Camera Glyph Filter Laurent RG Precision Exterior Skiff Trickle Weald Hatch Carrel Quarry
open Planned.PrimaryIntegral295 Place Carrier Flint Lagoon Yurt Next.Free
open scoped Classical ContDiff BigOperators Topology ENNReal
variable {G:Gauge}{I J:Type}{n p r t d e:ℕ}{u D C σ B W:ℝ}{h:0<σ}{S:Pack n (Ed G Cover)}
local notation "A"=>Loc G 1
-- engineering grade w component-wise, insensitive to basis or normalization. Also input grades 0. constant channels.
def Cockade (G:Gauge)(n _d w:ℕ)(F:Pack n (Ed G Cover)):Prop:=∀ (b:Fin n→ℕ)(t:ℕ)(s:Cargo t)(f:Fin n→Masked G),(t+∑ i,b i)<w → (∀ i,f i∈Place.rangeLt (Loc G 1→ℝ) (b i))→ sonic F (pal s) (Yurt.inlet ∘ f)=0 -- allow n0 weights etc
-- structural package. width used only liberties.
structure Tuned (G:Gauge)(n h d w:ℕ)(σ:ℝ)(hs:0<σ)(F:Pack n (Ed G Cover))(C:ℝ):Prop where
 coherent : Lyrics F
 meter : ∃ D:ℝ,0≤D∧Sings (stance _) d hs F D
 sturdy : Minored G h n F C
 onway : Cockade G n d w F
 nonneg : 0≤C

-- Epoka for rank, support is polynomial only.
abbrev eV:=Ed G Cover
-- `star` currency specialized to all for finite sums. even if different width between F validity and tuned. simply choose actual.
lemma permits_poly {h w:ℕ}{Y:ℝ}{W:Pack n (Ed G Cover)}{σ:ℝ}{hs:0<σ}(he:Tuned G n h d w σ hs W Y){V:Fin n→Masked G}{b:Fin n→ℕ}(hv:∀ i,V i∈Place.rangeLt _ (b i)):
 Voice (fun f=> sonic W f (Yurt.inlet ∘ V)):=by
 obtain ⟨D,hD,H⟩:=he.meter
 choose C hC using fun i=>chitQual (hv i)
 let p:=∑ i,b i
 let Z:= Yurt.star he.coherent H hD (X:=Yurt.inlet ∘ V) (a:=C) (δ:=0) (p:=p) le_rfl (by linarith) (fun i=> exhausted (hC i) (single_le_sum (f:=b) (fun _ _=>Nat.zero_le _) (mem_univ i)) le_rfl)
 exact voiced Z

-- weighted expansions Push.E for h weight ≤ n. hs same width. Vanilla n arbitrary. use dependent finite sums indexed by grades per dir via common index Fin (h+1) padded representation. cost multiplies V.tariff. Norm uses D*N^n u^w.
private lemma inlet_sum [Fintype I](f:I→Masked G): Yurt.inlet (∑ i,f i)=∑ i,Yurt.inlet (f i):=by
 funext i; unfold Yurt.inlet; simp only [Finset.sum_apply]
lemma sonic_poly_all [Fintype I]{h w:ℕ}{σ D:ℝ}{hs:0<σ}(he:Tuned G n h d w σ hs S D){F:Fin n→I→Masked G}{b:Fin n→I→ℕ}(hf:∀ i j,F i j∈ Place.rangeLt _ (b i j))(t:Pearl):
 sonic S t (fun i=>Yurt.inlet (∑ j,F i j))=∑ j:Tape n I,sonic S t (fun z=>Yurt.inlet (F z (j z))):=by
 obtain ⟨T,hT,H⟩:=he.meter
 simp_rw [Halo.inlet_sum]
 let p:=∑ i:Fin n,∑ j:I,b i j
 choose D hD using fun i j=>chitQual (hf i j)
 refine sonic_bill he.coherent H hT _ (X:=fun i j=>Yurt.inlet (F i j)) (a:=D) (δ:=0) (p:=p) le_rfl (by linarith) (fun i j=>exhausted (hD ..) ?_ le_rfl)
 exact (single_le_sum (f:=fun j=> b i j) (fun i (_:i∈univ)=> Nat.zero_le _) (mem_univ j)).trans (single_le_sum (f:=fun i=>∑ j:I,b i j) (fun _ (_:_ )=> Nat.zero_le _) (mem_univ i))
lemma chit_zero (G:Gauge)(r:ℕ){C:ℝ}(h:0≤C):Chit G r 0 C:=⟨Submodule.zero_mem _,h,fun i=>by simp; positivity⟩

lemma relay_payout (G:Gauge)(R:ℕ): ∃ C:ℝ,1≤C ∧ ∀ (b:Fin n→ℕ){V:Fin n→Masked G}{a:Fin n→ℝ}(q:ℕ){t:Pearl}{u E:ℝ},(∀ i,b i≤R)→q≤R→0<u→ (∀ i,Pool u (b i) 1 (V i) (a i))→Pool u (q+1) 0 t.val E→∃ (f:Fin n→Fin R→Masked G)(g:(i:Fin (R+1))→Cargo i.val→ℝ),
 (∀ i,V i=∑ j,f i j)∧ t=∑ i,∑ j,g i j • pal j ∧ (∀ i j,Chit G (j.val+1) (f i j) (C*a i*u^(j.val+1))) ∧ (∀ i j,|g i j|≤ C*E*u^i.val) ∧ (∀ (i:Fin n)(j:Fin R),b i≤j.val→f i j=0) ∧ (∀ i: Fin (R+1), q < i.val → ∀ j,g i j=0):=by
 choose D hD H using fun b=>parcel G b
 obtain ⟨W,hW,F⟩:=glossary (R+1)
 -- padding test preserve band+1 and pay but desired truncate above q; glossary q etc.
 choose K hK Z using glossary
 let C:=∑ i:Fin (R+2), (D i.val + K i.val)
 have hC(i:Fin (R+2)):D i.val+K i.val≤C:=single_le_sum (f:=fun i:Fin (R+2)=>D i.val+K i.val) (fun i _=>by have:=hD i.val;have:=hK i.val;linarith) (mem_univ _)
 have hD'(i:ℕ)(h:i≤R+1):D i≤C:= (le_add_of_nonneg_right (zero_le_one.trans (hK i))).trans (hC ⟨i,by omega⟩)
 have hK'(i:ℕ)(h:i≤R+1):K i≤C:=(le_add_of_nonneg_left (zero_le_one.trans (hD i))).trans (hC ⟨i,by omega⟩)
 refine ⟨C,(hD 0).trans (hD' 0 (by omega)),fun b V a q t u E hb hq hu hv ht=>?_⟩
 choose L hL hχ using fun i:Fin n=>H (b i) (V i) (D:=a i) hu (hv i)
 obtain ⟨P,hP,hπ⟩:=Z (q+1) t hu ht
 let f(i:Fin n)(j:Fin R):= if h:j.val<b i then L i ⟨j.val,h⟩ else 0
 let g (i:Fin (R+1))(j:Cargo i.val):ℝ:=if h:i.val<q+1 then P ⟨i.val,h⟩ j else 0
 refine ⟨f,g,?_,?_,?_,?_,?_,?_⟩
 · intro i; rw [hL i]
   let e:(Fin (b i))↪ Fin R:=Fin.castLEEmb (hb i)
   have H : ∑ j∈univ.map e,f i j=∑ j:Fin (b i),L i j:=by rw [sum_map];apply sum_congr rfl;intro j _;unfold f;rw [dif_pos (show (e j).val < b i from j.isLt)];rfl
   rw [←H];apply Finset.sum_subset (subset_univ _);intro j _ hj;unfold f;rw [dif_neg (by intro h;exact hj (mem_map_of_mem e (mem_univ (⟨j.val,h⟩:Fin (b i))))) ]
 · rw [hP]
   let e:(Fin (q+1))↪ Fin (R+1):=Fin.castLEEmb (Nat.add_le_add_right hq 1);let c(t:Fin (R+1)):=∑ j:Cargo t.val,g t j • pal j
   have H :∑ t∈univ.map e,c t=∑ t:Fin (q+1),∑ j,P t j • pal j:=by rw [sum_map];apply sum_congr rfl;intro j _;unfold c;simp_rw [g,dif_pos (show (e j).val<q+1 from j.isLt)];rfl
   rw [←H];apply Finset.sum_subset (subset_univ _);intro j _ hj;unfold c;simp_rw [g,dif_neg (show ¬j.val<q+1 from by intro h;exact hj (mem_map_of_mem e (mem_univ (⟨j.val,h⟩:Fin (q+1)))))];simp
 · intro i j;unfold f; have hk:=hv i|>.nice
   split
   · rename_i h; apply (hχ i ⟨j.val,h⟩).up (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hD' _ (by have:=hb i;omega)) hk) (pow_nonneg hu.le _))
   exact chit_zero _ _ (by have he:0≤C:=zero_le_one.trans ((hD 0).trans (hD' 0 (by omega))); positivity)
 · intro i j; unfold g;have hh:=ht.nice; split
   · rename_i h; exact (hπ ⟨i.val,h⟩ j).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hK' _ (by omega)) hh) (pow_nonneg hu.le _))
   rw [abs_zero]; have he:0≤C:=zero_le_one.trans ((hD 0).trans (hD' 0 (by omega))); positivity
 · intro i j h;unfold f;rw [dif_neg (by omega)]
 intro i h j; unfold g;rw [dif_neg (by omega)]
end YM.RG08.Halo
