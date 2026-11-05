import YM.RG08.Flint.Spat

/-!
# Coefficient contour off all periods, budget for marks evaluated on near
polynomials. No summability at rank-e needed until final polarization extension.
-/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Flint
open Forms Function Finset Jetty Lattice Isles Pert.Bulk Skiff Trickle
open Room Gallery Camera MvPolynomial Glyph Quarry Weald Hatch Carrel Laurent Filter Stationary
open scoped Classical ContDiff BigOperators Topology PowerSeries ENNReal
variable {I J:Type}{G:Gauge}{n l p e d:ℕ}{C δ a σ B:ℝ}{w:G.El}{h:0<σ}

lemma fret_constant (V:I→ℝ)(x:Tape n I):fret (kiosk V) x=PowerSeries.C (∏ j,V (x j)):=map_prod PowerSeries.C (fun j:Fin n=>V (x j)) univ|>.symm
def leanTag (X:Ed G Cover→ℝ)(U:Nd G Cover→ℝ)(w:G.El):Ed G Cover→ℝ:= settle w (X+grad U)
lemma bond_constant (f:Pearl)(V:I→ℝ)(F:Pack n I):bond F f (kiosk V) 0 = sonic F f (fun _=>V):=by
 unfold bond sonic;apply tsum_congr; intro i;rw [fret_constant,tap,PowerSeries.coeff_C,if_pos rfl];rfl
lemma bond_drop (f:Pearl)(V:I→ℝ)(F:Pack n I){k:ℕ}(hk:k≠0):bond F f (kiosk V) k=0:=by unfold bond;simp_rw [fret_constant,tap,PowerSeries.coeff_C,if_neg hk,mul_zero];exact tsum_zero
lemma bond_lean (f:Pearl)(V:Ed G Cover→ℝ)(U:Nd G Cover→ℝ)(F:Pack n (Ed G Cover)):
   bond F f (gain w (kiosk V) (kiosk U)) 0=sonic F f (fun _=>leanTag V U w):=by
 unfold bond sonic;apply tsum_congr; intro i
 rw [fret,tap,PowerSeries.coeff_zero_eq_constantCoeff_apply,map_prod];simp_rw [←PowerSeries.coeff_zero_eq_constantCoeff_apply];change F i f*(∏ j,tap 0 (gain w (kiosk V) (kiosk U) (i j)))=_;simp_rw [incoming];rfl
variable {X:Ed G Cover→ℝ}{U:Nd G Cover→ℝ}{M:GrainS (Ed G Cover)}
def desk (G:Gauge)(w:G.El)(p e n:ℕ)(a σ:ℝ):ℝ:= vendor G w p e a ^ n * blade 0 (p*((e+1)*n)) (σ/2)
lemma bend_cover (he:0≤δ)(hu:δ≤1)(hq:(↑((e+1)*n):ℝ)*δ≤σ/2)(ht:Bearing (stance (Loc G 1)) p δ a X)(hb:Bearing (stance G.ColorIndex) p δ a U){k:ℕ}(hk:k≤e)(h:0<σ):
 Covering (stance (Loc G 1)) σ n (desk G w p e n a σ) (fun x=>tap k (fret (gain w (kiosk X) (kiosk U)) x)):=by
 let L:=stance (Loc G 1);let Q:=(e+1)*n; let D:=blade 0 (p*Q) (σ/2)
 have hD:0≤D:=blade_nn _ _ (half_pos h).le
 let E:=vendor G w p e a; have hE:0≤E:=vendor_nn w p e ht.1
 refine ⟨mul_nonneg (pow_nonneg hE _) hD,fun x=>(fret_ward w he hu ht hb hk x).trans ?_⟩
 rw [hustle_pow]; change E^n*((1+L.cage x)^(p*Q)*Real.exp _ )≤ E^n*D*_
 apply (mul_le_mul_of_nonneg_left (mul_le_mul (hustle_fee (p*Q) (half_pos h) (L.cage_nn x)) (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hq (L.cage_nn _))) (Real.exp_pos _).le (mul_nonneg hD (Real.exp_pos _).le)) (pow_nonneg hE _)).trans_eq
 simp_rw [mul_assoc,← Real.exp_add,show σ/2*L.cage x+σ/2*L.cage x=σ*L.cage x by ring];rfl

lemma paid_cover (he:0≤δ)(hu:δ≤1)(hq:(↑((e+1)*n):ℝ)*δ≤σ/2)(ht:Bearing (stance (Loc G 1)) p δ a X)(hb:Bearing (stance G.ColorIndex) p δ a U){k:ℕ}(hk:k≤e){P:Pack n (Ed G Cover)}(f:Pearl)(hf:Lyrics P)(hB:0≤B)(hP:Sings (stance _) d h P B):
 |bond P f (gain w (kiosk X) (kiosk U)) k| ≤ desk G w p e n a σ * B * beam d h f:= (tote_sums P f h hf B hB hP (bend_cover he hu hq ht hb hk h)).2

-- finite fenced real probes on sparse ward, quantitative scaled diagonal. imports Permit for all later.
def Fenced (V:I→ℝ):Prop:= ∃ s:Finset I, ∀ i∉s,V i=0
lemma Fenced.zero :Fenced (0:I→ℝ):=⟨∅,fun _ _=>rfl⟩
lemma Fenced.add {x y:I→ℝ}(hx:Fenced x)(hy:Fenced y):Fenced (x+y):=by obtain ⟨s,hs⟩:=hx;obtain ⟨t,ht⟩:=hy;refine ⟨s∪t,fun i hi=>?_⟩; simp only [mem_union,not_or] at hi;rw [Pi.add_apply,hs i hi.1,ht i hi.2];exact add_zero _
lemma Fenced.smul {x:I→ℝ}(hx:Fenced x)(a:ℝ):Fenced (a • x):=by obtain ⟨s,hs⟩:=hx;exact ⟨s,fun i hi=>by rw [Pi.smul_apply,hs i hi];exact smul_zero _⟩
lemma Fenced.sum (s:Finset I)(f:I→J→ℝ)(he:∀ i∈s,Fenced (f i)):Fenced (∑ i∈s,f i):=by
 induction s using Finset.induction_on with
 | empty=>rw [sum_empty];exact Fenced.zero
 | @insert i s hi ih=>rw [sum_insert hi];exact (he i (by simp)).add (ih fun j hj=>he j (by simp [hj]))
lemma Fenced.kiosk {x:I→ℝ}(he:Fenced x):∃ u:Tray I,u.get=kiosk x:=by
 obtain ⟨s,hs⟩:=he; exact ⟨⟨s,Weald.kiosk x,fun i hi=>by rw [Weald.kiosk,hs i hi,map_zero]⟩,rfl⟩

lemma ward_awake (he:Calls l M)(w:G.El)(ht:Fenced X)(hu:Fenced U)(f:Pearl):awaken l M f (kiosk X)= awaken l M f (gain w (kiosk X) (kiosk U)):=by
 obtain ⟨s,hs⟩:=ht.kiosk; obtain ⟨t,ht⟩:=hu.kiosk;rw [←hs,←ht]; have hp:=he f s t w;change _= awaken l M f (portrait _ (art s t)).get;rw [woken,woken,hp]

-- Do not need bound on all e or on rank e to yield difference lower. price e used by caller.
lemma ward_range (he:Calls l M)(w:G.El)(ht:Fenced X)(hu:Fenced U)(f:Pearl):
 (∑ i∈range (l+e+1),sonic (M e i) f (fun _=>X))-(∑ i∈range (l+e+1),sonic (M e i) f (fun _=>leanTag X U w))=∑ k∈range e,∑ i∈ range (l+k+1),bond (M k i) f (gain w (kiosk X) (kiosk U)) (e-k):=by
 have hh:=congrArg (tap e) (ward_awake he w ht hu f); unfold tap awaken at hh;rw [PowerSeries.coeff_mk,PowerSeries.coeff_mk,sum_range_succ,Finset.sum_eq_zero (fun i (hi:i∈range e)=>Finset.sum_eq_zero fun n (_:n∈range (l+i+1))=>bond_drop f X (M i n) (show e-i≠0 from Nat.ne_of_gt (Nat.sub_pos_of_lt (mem_range.mp hi)))),zero_add,sum_range_succ (fun i=>∑ u∈range (l+i+1),bond (M i u) f (gain w (kiosk X) (kiosk U)) (e-i)),Nat.sub_self] at hh; simp_rw [bond_constant,bond_lean] at hh
 rw [hh]; ring

def junior (G:Gauge)(w:G.El)(p e l:ℕ)(a σ:ℝ):=∑ k∈range e,∑ i∈range (l+k+1),desk G w p e i a σ
lemma ward_lower (hp:0≤δ)(hs:δ≤1)(hz:(↑((e+1)*(l+e)):ℝ)*δ≤σ/2)(hq:Bearing (stance (Loc G 1)) p δ a X)(hx:Bearing (stance G.ColorIndex) p δ a U)
 (he:Calls l M)(hl:Permit d l M)(f:Pearl)(ht:Fenced X)(hu:Fenced U)(w:G.El)(hB:0≤B)(hM:∀ i<e,∀ k≤l+i,Sings (stance _) d h (M i k) B):
 |(∑ i∈range (l+e+1), sonic (M e i) f (fun _=>leanTag X U w))-(∑ i∈range (l+e+1), sonic (M e i) f (fun _=>X))| ≤ junior G w p e l a σ * (B * beam d h f):=by
 -- parenthesis ambiguities ∑ parse 
 rw [abs_sub_comm,ward_range he w ht hu f,junior,sum_mul]
 refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k hk=>?_);have hK:k<e:=mem_range.mp hk
 rw [sum_mul];apply (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i hi=>?_)
 have hI:i≤l+k:=by simp only [mem_range] at hi;omega
 obtain ⟨hL,_⟩:=hl.price k i
 rw [←mul_assoc];apply paid_cover hp hs _ hq hx (by omega) f hL hB (hM _ hK _ hI)
 exact le_trans (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.mul_le_mul_left (e+1) (hI.trans (Nat.add_le_add_left hK.le l))) hp) hz
end YM.RG08.Flint
