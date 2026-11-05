import YM.RG08.Trill.Cues
import YM.RG08.Halo.Tuners
/-! # Sings on Hermitian bracket ORDER unchanged from polynomial costs, even without listed
 Ward (for D before verifying color among terms). Orth stencil unwrap. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Trill
open Forms Function Finset Jetty Lattice Isles Pert.Bulk Skiff Trickle
open Room Gallery Camera Glyph Quarry Weald Hatch Carrel Laurent Filter Stationary Flint
open Planned.PrimaryIntegral295 Place Film Labels Source Source.Drops WardBin Parts Lagoon Yurt Halo
open scoped Classical ContDiff BigOperators Topology ENNReal ComplexConjugate Matrix.Norms.Frobenius
variable {G:Gauge}{d n p l e D k:ℕ}{σ B Q:ℝ}
local notation "E₀"=>Ed G Cover
local notation "Y"=>Snap G d
local notation "A₀"=>Loc G 1
variable (X:Labels.Frame G d)

lemma sampled_pure (j:Fin (d-1))(X:Taylor G j.val):sampled (Pi.single j X)∈ Place.rangeLt (Axis→G.Color) (j.val+2):=by
 rw [sampled_slot]
 nth_rw 1 [show variation X = (variation X - radialValue X) + radialValue X from by abel]
 apply Submodule.add_mem _ (Place.grows _ (show j.val+1≤j.val+2 by omega) (Place.variation_cost X)) _
 apply Place.vector_band;intro i
 change Tensor.diagonal (X.val i) ∈ _;exact Place.exact_le_band (by omega:j.val+1<j.val+2) (Place.simple _)
-- spend only basis single ticket. chip qual at ranked shape
lemma chip_price (G:Gauge)(d _p:ℕ):∃ C:ℝ,1 ≤ C ∧ ∀ b:Fin (d-1),∀ i: Fin (Labels.dim G b.val),
 Chit G (b.val+2) (Halo.depict G (sampled (@chip G d ⟨b,i⟩))) C:=by
 choose c h using fun v:WardBin.Board G d=>chitQual (Place.linear_band (Halo.bonnet G).symm.toContinuousLinearMap (v.1.val+2) (sampled_pure v.1 ((axes G v.1.val) v.2)))
 have hh(v:WardBin.Board G d):0≤c v:=(h v).live
 refine ⟨1+∑ v,c v,le_add_of_nonneg_right (Finset.sum_nonneg (fun v _=>hh v)),fun b i=> (h ⟨b,i⟩).up (le_trans (Finset.single_le_sum (f:=c) (fun v _=>hh v) (mem_univ (⟨b,i⟩:WardBin.Board G d))) (le_add_of_nonneg_left zero_le_one))⟩
lemma pluck_chip (v:WardBin.Board G d) : Yurt.inlet (Halo.depict G (sampled (chip v)))=pluck 1 (chip v):=funext fun i=>(pluck_lead _ i).symm
private abbrev tar (G:Gauge)(d p k:ℕ):= {i:Tape p (WardBin.Board G d)//depth i=k}
private lemma singleShape (a:X.Index):∃ C:ℝ,0 ≤ C ∧ ∀ M:Harp G d p,∀ B:ℝ,0 ≤ B→(∀ i:tar G d p k, |M (chip ∘ i.val)|≤B)→ |tally X p k a M|≤ C * B:=by
 let P(i:tar G d p k):=pointT (chip ∘ i.val)
 have hh(M:Harp G d p)(ht:∀ j,P j M=0): (tally X p k a) M=0:=by
   rw [tally_use]; have he:tile (paintBand M) k=0:=by unfold tile;apply Finset.sum_eq_zero;intro i hi;change MvPolynomial.C (↑(M (chip ∘ i)):ℂ) * _=_;rw [show M (chip ∘ i)=0 from ht ⟨i,(mem_filter.mp hi).2⟩];simp
   rw [he,map_zero];rfl -- indent
 obtain ⟨C,hC,H⟩:=court P hh (fun _=>1);exact ⟨C,hC,fun M B hB hx=>H B M hB (by intro g;rw [one_mul];exact hx g)⟩
-- for every F comparator, no invariance needed.each channel. Fees pure casts.
structure Ready (D:ℕ)(G:Gauge)(n:ℕ)(P:Pack n (Ed G Cover)):Prop where
 coherent: Lyrics P
 turned: ∀ f:Pearl,Forms.Sym (fun i=>P i f)
 well:∃(σ:ℝ)(h:0<σ)(C:ℝ),0≤C∧Sings (stance _) D h P C
lemma permit_ready {P: GrainS (Ed G Cover)}(h:Permit D l P):Ready D G n (P e n):=⟨(h.price e n).1,(fun f=> h.fine f e n),(h.price e n).2⟩
set_option synthInstance.maxHeartbeats 600000
set_option maxHeartbeats 800000
-- Compare allowing F,F' not color-invariant after splitting connected operations. ANY second scalar φ.
lemma single_chord (o:Accent X):∃ C:ℝ,0≤C ∧ let n:=(X.grades o.ear).2;let q:=weight o.test.play;∀ (F P:Pack n E₀)(D:ℕ)(r B:ℝ),Ready D G n F→Ready D G n P→0≤B→
 (∀ ψ:Fin n→Masked G,∀ b:Fin n→ℕ,∀ a:Fin n→ℝ,(∑ i,b i)=(X.grades o.ear).1→(∀ i,1≤b i)→(∀ i,Chit G (b i) (ψ i) (a i))→∀ s:Jetty.Cargo q,|sonic F (pal s) (Yurt.inlet ∘ ψ) -r* sonic P (pal s) (Yurt.inlet ∘ ψ)| ≤ B* (∏ i,a i))→
 |pix X o.ear o.test.play F - r*pix X o.ear o.test.play P| ≤ C*B:=by
 let n:=(X.grades o.ear).2;let m:=(X.grades o.ear).1
 obtain ⟨c,hC,h⟩:=singleShape (p:=n) (k:=m) X o.ear
 obtain ⟨V,hV,HV⟩:=chip_price G d n; let β:ℝ:=(beta o.test.play:ℝ)⁻¹;have hβ:0 ≤ β:=by unfold β;positivity
 refine ⟨c*(V^n)*β,by have hv:0 ≤ V:=by linarith
                      positivity,?_⟩
 intro _n q F P D r B hF hP hB hM
 let s:=concert o.test.play
 let N (x:Pack n E₀):=harrow x (celloTest o.test.play) n d
 have hh(i:tar G d n m)(x:Pack n E₀)(he:Ready D G n x): N x (chip ∘ i.val)=β * sonic x (pal s) (Yurt.inlet ∘ (fun j=>Halo.depict G (sampled (chip (i.val j))))) :=by
    obtain ⟨v,hv,c',hc',hg⟩:=he.well
    unfold N celloTest;rw [harrow_test (pal _) _ he.coherent hg hc',_root_.smul_apply,grants_chord he.coherent hg hc' (pal s) (he.turned _)];change β*_=_;congr 1; congr 1;funext j;exact (pluck_chip _).symm
 have hm(i:tar G d n m):|(N F-r • N P) (chip ∘ i.val)| ≤ V^n*β*B:=by
    have hx:=hM (fun j=>Halo.depict G (sampled (chip (i.val j)))) (fun j=>((i.val j).1.val+2)) (fun _=>V) (show (∑ j,((i.val j).1.val+2)) = m from i.property) (fun _=>by omega) (fun j=>HV ..) s
    rw [prod_const,card_univ,Fintype.card_fin] at hx
    change |N F _ - r*N P _|≤_; rw [hh i F hF,hh i P hP,mul_left_comm,←mul_sub,abs_mul,abs_of_nonneg hβ];exact (mul_le_mul_of_nonneg_left hx hβ).trans_eq (by ring)
 have hd:0 ≤ V:=zero_le_one.trans hV
 have hz:= h (N F-r • N P) (V^n*β*B) (by positivity) hm
 rw [map_sub,_root_.map_smul,smul_eq_mul] at hz;exact hz.trans_eq (by ring)
end YM.RG08.Trill
