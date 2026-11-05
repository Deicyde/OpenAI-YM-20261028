import YM.RG08.Sideshow.Elevation
/-! # Solve the SAME l column equation using leading inverse, no post
 on repeated component.
 -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Sideshow
open Forms Function Finset Jetty Lattice Isles Pert.Bulk Stationary Spar Camera Glyph Filter Room Laurent RG Precision Exterior Skiff Trickle Weald Hatch Carrel Quarry Steam
open Planned.PrimaryIntegral295 Place Film Labels Source Source.Drops WardBin Parts Flint Lagoon Yurt Next.Free Atrium Trill Necks
open scoped Classical ContDiff BigOperators Topology ENNReal PowerSeries Matrix
variable {G:Gauge}{n D d p l e k c j t:ℕ}{σ τ μ V Q B C δ η a b W:ℝ}{P:Patch}{K:KernelChoices}
variable (X:Labels.Frame G d)
local notation "I₀"=> Accent X
local notation "M₀"=>Playbook X
local notation "S₀"=>Bouquet X
local notation "A₀"=>Loc G 1
local notation "E"=>Ed G Cover
local notation "∆"=>stance A₀

def booth (l:ℕ):Finset I₀:=Finset.filter (fun i=> octave i=l) univ
lemma booth_in {i:I₀}:i∈booth X l ↔ octave i=l:=by simp [booth]

def ice (M:M₀)(l:ℕ)(U:I₀→Pack n E)(i:I₀):Pack n E:=∑ j∈booth X l,ink M j i • U j
def rinks (M:M₀)(l:ℕ)(U:I₀→Pack n E)(i:I₀):Pack n E:=∑ j:I₀,if j∈booth X l then 0 else ink M j i • U j
def skein (M:M₀)(S:S₀)(e n:ℕ)(i:I₀):Pack n E:=∑ j:I₀,∑ a∈(range (e+1)).erase 0,tap a (M j i) • S j (e-a) n
lemma ice_pay (M:M₀)(l:ℕ)(U:I₀→Pack n E)(i:I₀):(∑ j:I₀,ink M j i • U j)=ice X M l U i+rinks X M l U i:=by
 unfold ice rinks booth;rw [sum_filter,←sum_add_distrib];apply sum_congr rfl;intro j _;simp [mem_filter];split_ifs <;> simp
lemma below (M:M₀)(S:S₀)(i:I₀)(e n l:ℕ):
 let F(j:I₀):=S j e n
 ; Atrium.shuffle M S i e n=ice X M l F i+(rinks X M l F i + skein X M S e n i):=by
 intro F;rw [←add_assoc,←ice_pay];unfold skein Atrium.shuffle;rw [Finset.sum_apply,Finset.sum_apply,←sum_add_distrib];apply sum_congr rfl;intro j _
 unfold Atrium.slip;rw [←add_sum_erase _ _ (show 0∈range (e+1) from mem_range.mpr (Nat.zero_lt_succ _)),Nat.sub_zero];rfl
lemma invertMix {M B:M₀}(h:Wins M B)(ht:Cloth M)(l:ℕ)(T:I₀→Pack n E):∀ i∈booth X l,ice X B l (ice X M l T) i=T i:=by
 intro i hi;unfold ice; simp_rw [Finset.smul_sum,smul_smul];rw [sum_comm];simp_rw [←Finset.sum_smul]
 have hz:dusk 0 (M*B) = ink M* ink B:=by rw [dusk_mul];simp only [zero_add,range_one,sum_singleton,Nat.sub_zero];rfl
 have hv:ink M * ink B=1:=hz.symm.trans (by rw [h.right,dusk_one,if_pos rfl])
 have hv'(j)(hj:j∈booth X l):(∑ k∈booth X l,ink B k i * ink M j k)=if i=j then 1 else 0:=by
    have ha(i j:I₀)(he:ink M i j≠0):octave i≤octave j:=Nat.le_of_not_gt fun h=>he (ht i j 0 h)
    have hb(i j:I₀)(he:ink B i j≠0):octave i≤octave j:=Nat.le_of_not_gt fun h' =>he (h.leading0Cloth i j 0 h')
    rw [eq_comm (a:=i) (b:=j),← Matrix.one_apply (α:=ℝ) (i:=j) (j:=i),←hv,Matrix.mul_apply] -- binder names maybe
    simp_rw [mul_comm (ink B _ i)] -- only once? use Eq.trans
    apply Finset.sum_subset (Finset.subset_univ _);intro k _ hk;by_contra hN
    have hp:=ha _ _ (left_ne_zero_of_mul hN);have hq:=hb _ _ (right_ne_zero_of_mul hN); rw [booth_in] at hi hj hk;omega
 rw [Finset.sum_eq_single i];rw [hv' _ hi,if_pos rfl,one_smul]
 · intro j hj hu;rw [hv' j hj,if_neg (Ne.symm hu),zero_smul]
 exact fun h=>False.elim (h hi)
-- typo swapped diag if he i=j vs j=i
lemma flock (M B:M₀)(he:Wins M B)(ht:Cloth M)(e n:ℕ)(F S:S₀)(hF:F=Atrium.shuffle M S){i:I₀}(hi:i∈booth X l):
 let U(j:I₀):=F j e n-(rinks X M l (fun s=>S s e n) j+skein X M S e n j)
 ; S i e n=ice X B l U i:=by
 intro U;unfold U;rw [hF];simp_rw [below X M S _ e n l,add_sub_cancel_right];exact (invertMix X he ht l (fun i=>S i e n) i hi).symm

-- Budget for tails. constant accounting requests. index DAG earlier-tranche on mark: `e` then `l` then compare `n`. T matrix earlier entries at smaller deg all; same deg-to at rank≥n; Y=S renamed on buffer output. BoolPair includes T.Post0 precision all. χ δ. Equip absol too. 
structure Candor {D d:ℕ}{σ:ℝ}(h:0<σ)(X:Labels.Frame G d)(e l n:ℕ)(S T:Bouquet X)(M V:Playbook X)(B δ:ℝ):Prop where
 safe:0≤B
 rate:0≤δ
 samples:∀ c:Trill.Accent X,∀ i k,i<e ∨ i=e∧ (octave c<l) →Dyad (stance _) D h B δ (S c i k) (T c i k)
 pulse:∀ c:Accent X,octave c=l→∀ s:Accent X,∀ i,i<e∨i=e ∧ n ≤ octave s→
   |tap i (M s c)|≤B ∧ |tap i (V s c)|≤B ∧ |tap i (M s c)-tap i (V s c)|≤ B*δ
 -- NOTE: e=0 & s<l with n≤octave s includes T same order, as needed.

lemma pantry {S T:S₀}{M N:M₀}{h:0<σ}(hf:Threads D S)(hp:Threads D T)(he:Cloth M)(hu:Cloth N)(hd:Candor (D:=D) h X e l n S T M N b δ)(i:I₀)(hi:octave i=l):
 let A(j:I₀):=S j e n;let A'(j:I₀):=T j e n
 let w:ℝ:=Fintype.card I₀*(1+(e:ℝ)+1)* (2*b*b)
 ; Dyad ∆ D h w δ (rinks X M l A i+skein X M S e n i) (rinks X N l A' i+skein X N T e n i):=by
 intro A A' w
 let L(j:I₀):= ink M j i;let L'(j:I₀):=ink N j i
 have hz:=hd.safe
 have h1(k:I₀):Dyad ∆ D h (2*b*b) δ (if k∈booth X l then 0 else L k • A k) (if k∈booth X l then 0 else L' k • A' k):=by
    split_ifs with hu'
    · exact (Dyad.zero hd.rate).mono (by positivity)
    by_cases hK:l < octave k
    · rw [show L k=0 from he k i 0 (by omega),show L' k=0 from hu k i 0 (by omega),zero_smul,zero_smul]
      exact (Dyad.zero hd.rate).mono (by positivity)
    rw [booth_in] at hu';have hY:=hd.samples k e n (.inr ⟨rfl,Nat.lt_of_le_of_ne (Nat.le_of_not_gt hK) hu'⟩)
    by_cases h': (0:ℕ)<e∨ n≤octave k
    · obtain ⟨h₁,h₂,h₃⟩:= hd.pulse i hi k 0 (by omega)
      exact hY.livery h₁ h₂ h₃
    have hg:octave k+e<n:=by omega
    rw [show A k=0 from Classical.not_not.mp fun hx=>by have hv: n ≤ octave k+e:= (hf k).1.lit e _ hx;omega, show A' k=0 from Classical.not_not.mp fun hx=>by have hv:n≤octave k+e:= (hp k).1.lit _ _ hx;omega,smul_zero,smul_zero]
    exact (Dyad.zero hd.rate).mono (by positivity)
 let α:= (range (e+1)).erase 0
 have h2(k:I₀)(j:ℕ)(hj:j∈α):
    Dyad ∆ D h (2*b*b) δ (tap j (M k i) • S k (e-j) n) (tap j (N k i) • T k (e-j) n):=by
    obtain ⟨hK,hR⟩:= mem_erase.mp hj; have hv:= mem_range.mp hR
    by_cases h:j<e∨n≤octave k
    · obtain ⟨h₁,h₂,h₃⟩:=hd.pulse i hi k j (by omega)
      exact (hd.samples k (e-j) n (.inl (by omega))).livery h₁ h₂ h₃
    rw [show S k (e-j) n=0 from Classical.not_not.mp fun H=>by have :=(hf k).1.lit _ _ H;omega,show T k (e-j) n=0 from Classical.not_not.mp fun H=>by have := (hp k).1.lit _ _ H; omega,smul_zero,smul_zero]; exact (Dyad.zero hd.rate).mono (by positivity)
 unfold rinks skein;apply ((Dyad.sum (C:=fun _=> 2*b*b) univ (fun k _=>h1 k) hd.rate).add (Dyad.sum (C:=fun _=>∑ _i∈α,2*b*b) univ (fun k _=>Dyad.sum α (h2 k) hd.rate) hd.rate)).mono
 unfold α
 simp only [sum_const,nsmul_eq_mul,card_univ, show (((range (e+1)).erase 0).card=e) from by rw [Finset.card_erase_of_mem (show 0∈range (e+1) by simp),card_range];simp]
 unfold w; nlinarith only [hz,Nat.cast_nonneg (α:=ℝ) e,Nat.cast_nonneg (α:=ℝ) (Fintype.card I₀),show 0≤(Fintype.card I₀:ℝ)*(b*b) by positivity]

lemma stir (M:M₀)(l:ℕ)(U V:I₀→Pack n E)(i:I₀): ice X M l (U-V) i=ice X M l U i-ice X M l V i:=by unfold ice;simp_rw [Pi.sub_apply,smul_sub,sum_sub_distrib]
-- Y_r differences when changing diagonal, via direct difference equation.
lemma canal {U S U' T:S₀}{M N V:M₀}(hf:U=Atrium.shuffle M S)(hh:U'=Atrium.shuffle N T)(hM:Cloth M)(he:Wins M V){i:I₀}(hi:i∈booth X l):
 let Y(j:I₀):=S j e n;let Y'(j:I₀):= T j e n
 let H(j:I₀):=U j e n;let H'(j:I₀):=U' j e n
 let δ(j:I₀):= rinks X M l Y j+skein X M S e n j;let τ(j:I₀):=rinks X N l Y' j+skein X N T e n j
 ; (Y-Y') i=ice X V l (fun j=>H j-H' j-(δ j-τ j)-(ice X M l Y' j-ice X N l Y' j)) i:=by
 intro Y Y' H H' Δ τ
 symm
 trans ice X V l (ice X M l (Y-Y')) i;swap;exact invertMix X he hM _ _ i hi
 unfold ice at * -- remove? want only V; funext integrand
 apply congrArg (fun (F:I₀→Pack n E)=> ∑ j∈booth X l,(ink V j i) • F j)
 funext c
 change H c-H' c-(Δ c-τ c)-(ice X M l Y' c-ice X N l Y' c)=ice X M l (Y-Y') c
 have hz:H c=ice X M l Y c+Δ c:=by unfold H;rw [hf];exact below ..
 have hz':H' c=ice X N l Y' c+τ c:=by unfold H';rw [hh];exact below ..
 rw [stir,hz,hz'];abel

local notation "Icd" => (Fintype.card (Accent X) : ℝ)
lemma ice_price {k:Side}{M:M₀}{q b:ℝ}(hc:0≤q)(hb:0≤b)(hX:Monogram X k q M)(U:I₀→Pack n E)(i:I₀){σ:ℝ}{h:0<σ}(hs:∀ j:I₀,octave j=l→ Sings ∆ D h (U j) b)(hi:octave i=l):
 let V:=evacuate M (fun i=>(k.val:ℝ)^(d-gamut i));
 Sings ∆ D h (ice X V l U i) (Icd*plum (Accent X) d q*b):=by
 intro V
 have ht:=hX.funded
 let P:ℝ:=plum I₀ d q;have hP:0≤P:=plum_nn hc
 have hw(j:I₀)(he:j∈booth X l): |ink V j i|≤P:=by
    change |dusk 0 (evacuate M _) _ _|≤_;rw [evacuate,deputy_home]
    have h := inverse_price Atrium.street hc ht hX.pace j i (show octave j=octave i from (booth_in X|>.mp he).trans hi.symm)
    exact h.trans (mul_le_of_le_one_left hP (inv_le_one_of_one_le₀ (gauge_scale X _ j)))
 unfold ice;apply (Sings.sum (booth X l) (a:=fun j=>|ink V j i| * b) (fun j hj=>(hs j (booth_in X|>.mp hj)).smul _) (fun j _=>mul_nonneg (abs_nonneg _) hb)).mono le_rfl le_rfl (fun _=>le_rfl)
 apply (sum_le_sum (g:=fun _=>P*b) (fun j hj=>mul_le_mul_of_nonneg_right (hw j hj) hb)).trans
 rw [sum_const,nsmul_eq_mul,←mul_assoc];gcongr; exact Finset.card_le_univ _
lemma axisDiff (M N:M₀)(B V δ:ℝ)(hV:0≤V)(hB:0≤B)(hδ:0≤δ)(Y:I₀→Pack n E)(i:I₀){h:0<σ}(hs:∀ j:I₀,octave j=l→ Sings ∆ D h (Y j) V)(he:∀ j:I₀,octave j=l→ |ink M j i - ink N j i|≤B*δ):
 Sings ∆ D h (ice X M l Y i-ice X N l Y i) (Icd*B*δ*V):=by
 unfold ice;rw [←sum_sub_distrib];simp_rw [←sub_smul]
 have H(j:I₀)(hj:j∈booth X l):Sings ∆ D h ((ink M j i-ink N j i) • Y j) (B*δ*V):=((hs j ((booth_in X).mp hj)).smul _).mono le_rfl le_rfl (fun _=>le_rfl) (mul_le_mul_of_nonneg_right (he j ((booth_in X).mp hj)) hV)
 apply (Sings.sum (a:=fun _=>B*δ*V) (booth X l) H (fun _ _=>by positivity)).mono le_rfl le_rfl (fun _=>le_rfl)
 rw [sum_const,nsmul_eq_mul];apply le_trans (mul_le_mul_of_nonneg_right (show (#(booth X l):ℝ)≤ Icd by exact_mod_cast Finset.card_le_univ (booth X l)) (by positivity : 0≤B*δ*V));apply le_of_eq;ring
-- absolute only using matching real sections. sharpen Δ below.
lemma answer {σ a t u B:ℝ}{W:Side}{h:0<σ}{S:S₀}{Y:S₀}{M:M₀}(hc:0≤C)(hf:Monogram X W C M)(hs:Cloth M)(he:Wins M (evacuate M (fun i=>(W.val:ℝ)^(d-gamut i))))(hQ:Y=Atrium.shuffle M S)(hS:Threads D S)(hB:Candor (D:=D) h X e l n S S M M B 1)(ha:0≤a)(ht:0 ≤ t)(hu:0≤u)
 (hp:∀ i,octave i=l→Sings ∆ D h (Y i e n) (a*t/(W.val:ℝ)+u)):
 ∀ i,octave i=l→Sings ∆ D h (S i e n) ((Icd*plum I₀ d C*a)*t/(W.val:ℝ)+ Icd*plum I₀ d C*(u+Icd*(e+2:ℝ)*(2*B*B))):=by
 intro i hi
 let P:=evacuate M (fun i:I₀=>(W.val:ℝ)^(d-gamut i))
 let Z(j:I₀):=rinks X M l (fun s=>S s e n) j+skein X M S e n j
 let G'(j:I₀):=Y j e n-Z j
 have h1: S i e n=ice X P l G' i:=flock X M P he hs e n Y S hQ ((booth_in X).mpr hi)
 let p:=plum I₀ d C;let q:ℝ:= W.val; let D':ℝ:=Icd;let v:=D'*(e+2:ℝ)*(2*B*B);have hd:0≤D':=Nat.cast_nonneg _;have h0:0<q:=Nat.cast_pos.mpr W.pos;have hv:0≤v:=by unfold v;have h:=hB.safe; positivity
 rw [h1,show (Icd*p*a)*t/(W.val:ℝ)+ Icd*p*(u+Icd*(e+2:ℝ)*(2*B*B))=Icd*p*(a*t/q+u+v) from ?_];swap; · unfold q v D'; ring
 apply ice_price X hc (by positivity) hf G' i _ hi
 intro j hj; have h3:=pantry X hS hS hs hs hB j hj; dsimp only at h3
 apply (hp j hj).sub (show Sings ∆ D _ (Z j) v from ?_) (by positivity) hv
 have hh:Icd*(e+2:ℝ)*(2*B*B)=Icd*(1+ (e:ℝ)+1)*(2*B*B):=by ring
 unfold v D';rw [hh];exact h3.near

lemma answer_delta {σ a t u q B:ℝ}{W:Side}{h:0<σ}{S S' Y Y':S₀}{M N:M₀}(hc:0≤C)(hf:Monogram X W C M)(hs:Cloth M)(hN:Cloth N)
 (hQ:Y=Atrium.shuffle M S)(hQ':Y'=Atrium.shuffle N S')(hS:Threads D S)(hS':Threads D S')(hB:Candor (D:=D) h X e l n S S' M N B δ)(ha:0≤a)(ht:0 ≤ t)(hu:0≤u)(hn:n≤l+e)
 (hp:∀ i,octave i=l→Sings ∆ D h (Y i e n-Y' i e n) (a*t/(W.val:ℝ)+u*δ))(hP:0≤q)(hr:∀ i,octave i=l→Sings ∆ D h (S' i e n) q):
 ∀ i,octave i=l→Sings ∆ D h (S i e n-S' i e n) ((Icd*plum I₀ d C*a)*t/(W.val:ℝ)+ Icd*plum I₀ d C*(u+Icd*(e+2:ℝ)*(2*B*B)+ Icd*B*q)*δ):=by
 let A':= evacuation hs hf.funded
 let E':Hearth I₀:=ink (evacuate M (fun i:I₀=>(W.val:ℝ)^(d-gamut i)))
 intro i hi;rw [show S i e n-S' i e n=_ from (canal X hQ hQ' hs A' ((booth_in X).mpr hi))]
 let s:=plum I₀ d C;let w:ℝ:= W.val; let D':ℝ:=Icd;let v:=D'*(e+2:ℝ)*(2*B*B);have hd:0≤D':=Nat.cast_nonneg _;have h0:0<w:=Nat.cast_pos.mpr W.pos;have hv:0≤v:=by unfold v;have h:=hB.safe; positivity
 rw [show D'*s*a*t/(W.val:ℝ)+ Icd*s*(u+Icd*(e+2:ℝ)*(2*B*B)+Icd*B*q)*δ=Icd*s*(a*t/w+u*δ+v*δ+Icd*B*δ*q) from ?_];swap; · unfold w v D'; ring
 have hδ:=hB.rate;have hW:=hB.safe;apply ice_price X hc (by positivity) hf _ i _ hi;intro j hj
 apply ((hp j hj).sub (show Sings ∆ D h _ (v*δ) from ?_) (by positivity) (mul_nonneg hv hδ)).sub _ (add_nonneg (by positivity) (mul_nonneg hv hδ)) (by positivity);swap
 · apply axisDiff X M N B q δ hP hW hδ (fun i=>S' i e n) j hr;intro s hs
   exact ((hB.pulse j hj s 0 (by omega)).2.2)
 have h1:= pantry X hS hS' hs hN hB j hj;unfold v D';rw [show (e+2:ℝ)=1+(e:ℝ)+1 by ring]; exact h1.switch
end YM.RG08.Sideshow
