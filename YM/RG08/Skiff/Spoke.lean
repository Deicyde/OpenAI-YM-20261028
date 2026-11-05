import YM.RG08.Skiff.Pair
import YM.RG08.Steam.Routing

/-!
# One-mark connected HJ recipes

Computes response of the normalized log (time parameter), one mark, hence
weights of fuse doubled (Γ symmetric in the diagram applications).
Proof this gives the intended normalized transfer in subsequent milestones.
Strict bill conditional on bulk Wire/V. Sym at order zero needs S symmetric separately.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Skiff
open Function Finset Jetty Forms Steam
open scoped BigOperators Topology ENNReal Classical
variable {I:Type}{m n i d j e p q l r a:ℕ}{σ δ W U:ℝ}{h:0<σ}{L:Loom I}{A:Ground I}
abbrev GrainS (I:Type):= (e n:ℕ)→Pack n I
abbrev Trips (I:Type):=ℕ→GrainS I
def ship(h:p=q)(F:Pack p I):Pack q I:= h ▸ F
lemma empty_ship (h:p=q):ship h (0:Pack p I)=0:=by subst h;rfl

def shim (Γ:Forms.Line I)(S:GrainS I)(e n:ℕ):Pack n I:=(((n:ℝ)+2)*(n+1)/2) • pocket Γ (S e (n+2))
def shift (Γ:Forms.Line I)(F:Pack (p+1) I)(V:Flake (q+1) I)(n:ℕ):Pack n I:=if h:p+q=n then (((p:ℝ)+1)*(q+1)) • ship h (cloak Γ F V) else 0
def rungs (Γ:Forms.Line I)(V:Steam.Grain I)(S:Trips I)(j e n:ℕ):Pack n I:=shim Γ (S j) e n+
   ∑ c∈range (n+1),∑ i∈range (j+1),∑ a∈range (e+1),shift Γ (S i a (c+1)) (Steam.burn Γ V (j-i) (e-a) (n-c+1)) n

def build (Γ:Forms.Line I)(V:Steam.Grain I)(F:GrainS I) : ℕ→Trips I
 | 0=> fun i=>if i=0 then F else 0
 | t+1=>update (build Γ V F t) (t+1) (fun e n=> ((t+1:ℝ)⁻¹) • rungs Γ V (build Γ V F t) t e n)
def skate (Γ:Forms.Line I)(V:Steam.Grain I)(F:GrainS I)(j:ℕ):GrainS I:=build Γ V F j j
variable (Γ:Forms.Line I)(V:Steam.Grain I)(F:GrainS I)
lemma early {i j:ℕ}(he:i≤j):build Γ V F j i=skate Γ V F i:=by
 induction j, he using Nat.le_induction with
 | base=>rfl
 | succ j hj ih=>rw [build,update_of_ne (by omega:i≠j+1),ih]
lemma start : skate Γ V F 0=F:=by simp [skate,build]
lemma climbs (j e n:ℕ): skate Γ V F (j+1) e n=((j+1:ℝ)⁻¹) • rungs Γ V (skate Γ V F) j e n:=by
 rw [skate,build,update_self]; congr 1; unfold rungs;rw [early Γ V F (i:=j) le_rfl]; congr 1;apply Finset.sum_congr rfl; intro i _;apply Finset.sum_congr rfl; intro x hx
 rw [early Γ V F (i:=x) (by simpa [Nat.lt_succ_iff] using hx)]
variable {Γ V F}{Γ':Forms.Line I}{V':Steam.Grain I}{F':GrainS I}

lemma stillwater:breeze (0:Pack n I)=0:=by
 unfold breeze;simp only [show (pattern (I:=I) (n:=n) · (0:Pack n I))=(fun _=> 0) from rfl,sum_const_zero,smul_zero]
lemma skimp {S:GrainS I}(h:S e (n+2)=0):shim Γ S e n=0:=by
 unfold shim pocket; rw [h,show (decker (nut Γ (0:Pack (n+2) I)))=0 from ?_,stillwater,smul_zero]; ext; simp [nut,decker]
lemma cold_l {G:Flake (q+1) I}:shift Γ (0:Pack (p+1) I) G n=0:=by
 unfold shift cloak; rw [show decker (sleeve Γ (0:Pack (p+1) I) G)=0 from ?_,stillwater];split_ifs<;>simp [empty_ship];ext;simp [sleeve,decker]
lemma cold_r {H:Pack (p+1) I}:shift Γ H (0:Flake (q+1) I) n=0:=by
 unfold shift cloak; rw [show decker (sleeve Γ H (0:Flake (q+1) I))=0 from ?_,stillwater];split_ifs<;>simp [empty_ship];ext;simp [sleeve,decker]

def Lit (l:ℕ)(F:GrainS I):Prop:=∀ e n,F e n≠0→n≤l+e
lemma sat (h:skate Γ V F (j+1) e n ≠0):skate Γ V F j e (n+2)≠0 ∨ ∃ c≤n,∃ i≤j, ∃ a≤e,skate Γ V F i a (c+1)≠0∧ Steam.burn Γ V (j-i) (e-a) (n-c+1)≠0:=by
 contrapose! h
 rw [climbs,rungs,skimp h.1,zero_add];convert smul_zero (A:=Pack n I) ((j+1:ℝ)⁻¹) using 2
 apply sum_eq_zero; intro c hc;apply sum_eq_zero;intro i hi;apply sum_eq_zero;intro a ha
 simp only [mem_range] at hc hi ha
 by_cases he:skate Γ V F i a (c+1)=0; · rw [he]; exact cold_l
 rw [h.2 c (by omega) i (by omega) a (by omega) he]; exact cold_r

theorem full (he:Lit l F)(hv:Steam.Eligible V)(hs:skate Γ V F j e n≠0):n+2*j≤l+3*e∧n≤l+e:=by
 induction j using Nat.strong_induction_on generalizing e n with
 | h j ih=> cases j with
   | zero=>rw [start] at hs;have ht:=he e n hs;omega
   | succ j=> obtain hs|⟨c,hc,i,hi,a,ha,h₁,h₂⟩:=sat hs
              · have ht:=ih j (by omega) hs;omega
              have ht:=ih i (by omega) h₁
              obtain ⟨hh,hm,_,hy⟩:=Steam.preserves hv _ _ _ h₂;omega

def spin (l:ℕ)(Γ:Forms.Line I)(V:Steam.Grain I)(F:GrainS I)(t:ℝ):GrainS I:=fun e n=>∑ j∈range (l+3*e+1),t^j • skate Γ V F j e n
def shaker (l:ℕ)(Γ:Forms.Line I)(V:Steam.Grain I)(F:GrainS I)(t:ℝ):GrainS I:=fun e n=> ∑ j∈range (l+3*e), t^(j+1) • skate Γ V F (j+1) e n
lemma cruising (t:ℝ):spin l Γ V F t=F+shaker l Γ V F t:=by
 ext e n:2; simp only [spin,shaker,sum_range_succ',Pi.add_apply,start,pow_zero,one_smul, add_comm (F e n)]

-- Lean trap names Hp, hp
lemma Dyad.ship {F F':Pack p I}(he:Dyad L d h U δ F F')(eq:p=n):Dyad L d h U δ (ship eq F) (ship eq F'):=by subst eq;exact he
lemma clamp {F F':GrainS I}(hg:WireCot A σ δ W Γ Γ')(hf:Dyad L d h U δ (F e (n+2)) (F' e (n+2))):Dyad L d h ((((n:ℝ)+2)*(n+1)/2)*(2*U*W)) δ (shim Γ F e n) (shim Γ' F' e n):=by
 simpa only [shim,abs_of_nonneg (by positivity:(0:ℝ)≤((n:ℝ)+2)*(n+1)/2)] using (hf.pocket hg).smul (((n:ℝ)+2)*(n+1)/2)
lemma click {K:ℝ}{P P':Pack (p+1) I}{Y Y':Flake (q+1) I}(he:fits L A)(hg:WireCot A σ δ W Γ Γ')(hf:Dyad L d h U δ P P')(hy:Cot A σ δ K Y Y') : Dyad L d h ((((p:ℝ)+1)*(q+1))*(3*(U*W*K))) δ (shift Γ P Y n) (shift Γ' P' Y' n):=by
 unfold shift; split_ifs with H
 · simpa only [abs_of_nonneg (by positivity:(0:ℝ)≤((p:ℝ)+1)*(q+1))] using ((Dyad.cloak he hf hg hy).ship H).smul (((p:ℝ)+1)*(q+1))
 have ha:=hf.price; have hb:=hy.gain;have hc:=hg.near.gain
 exact (Dyad.zero hf.rate).mono (by positivity)

def across (j e n a r:ℕ):=a<e ∨ a=e∧(n<r ∨ j=0∧n=r)

/-- Conditional rough source cost per scale. Nonzero heat uses only **higher** rank at same
coupling order (include scalar output exactly, no scalar input to vacuum). Distinct U supports
induction without charging irrelevant lower-rank marked components. Covers differences of every
input datum including Γ, V, assuming V as in the same-bulk prescription. Polynomial fees
independent of geometries and slots index types, exponential σ carried through. -/
theorem journey (j e n:ℕ):∃ P:ℝ→ℝ,Wage P∧
 ∀ {I:Type}(A:Ground I)(L:Loom I){σ:ℝ}(h:0<σ)(d:ℕ)(δ W U:ℝ)(V V':Steam.Grain I)(Γ Γ':Forms.Line I)(F F':GrainS I),
 fits L A→Eligible V→Eligible V'→WireCot A σ δ W Γ Γ'→ 0≤δ→1≤W→0≤U→
 (∀ a r,taps 0 e 0 a r→Cot A σ δ W (V a r) (V' a r))→(∀ a r,across j e n a r→Dyad L d h U δ (F a r) (F' a r))→Dyad L d h (P W*U) δ (skate Γ V F j e n) (skate Γ' V' F' j e n):=by
 induction j using Nat.strong_induction_on generalizing e n with
 | h j ih=> cases j with
   | zero=> refine ⟨_,Wage.constant (1:ℝ) zero_le_one,?_⟩
            intro I A L σ h d δ W U V V' Γ Γ' F F' _ _ _ _ _ _ _ _ ha
            rw [start,start,one_mul]; exact ha _ _ (Or.inr ⟨rfl,Or.inr ⟨rfl,rfl⟩⟩)
   | succ j=>
     obtain ⟨P,hP,HP⟩:=ih j (by omega) e (n+2)
     choose Q hQ HQ using fun i b k=>ih (min i j) (by omega) b k
     choose R hR HR using fun i b k:ℕ=> Steam.navigation (j-i) b k
     let N (x:ℝ):ℝ:= (((n:ℝ)+2)*(n+1)/2)*(2*P x*x)
     let M (x:ℝ)(c i a:ℕ):ℝ:= ((c:ℝ)+1)*((↑(n-c):ℝ)+1)*(3*(Q i a (c+1) x*x*R i (e-a) (n-c+1) x))
     let S(x:ℝ):=∑ c∈range (n+1),∑ i∈range (j+1),∑ a∈range (e+1),M x c i a
     have hN:Wage N:=(Wage.constant _ (by positivity)).mul (((Wage.constant 2 (by norm_num)).mul hP).mul Wage.input)
     have hM (c i a:ℕ):Wage fun x=>M x c i a:=(Wage.constant _ (by positivity)).mul ((Wage.constant 3 (by norm_num)).mul (((hQ ..).mul Wage.input).mul (hR ..)))
     have hT:Wage S:= Wage.sum _ _ fun c _=> Wage.sum _ _ fun i _=> Wage.sum _ _ fun a _=>hM c i a
     refine ⟨_,(Wage.constant |((j+1:ℝ)⁻¹)| (abs_nonneg _)).mul (hN.add hT),?_⟩
     intro I A L σ h d δ W U V V' Γ Γ' F F' hf hv hv' hΓ hδ hW hU hG ha
     rw [climbs,climbs,mul_assoc,add_mul]; apply Dyad.smul; unfold rungs; apply Dyad.add
     · convert clamp hΓ (HP A L h d δ W U V V' Γ Γ' F F' hf hv hv' hΓ hδ hW hU hG (fun a r hh=>ha a r ?_)) using 1
       · unfold N;ring
       unfold across at *;omega
     unfold S; rw [Finset.sum_mul]; refine Dyad.sum _ (fun c hc=>?_) hδ; rw [Finset.sum_mul]; refine Dyad.sum _ (fun i hi=>?_) hδ; rw [Finset.sum_mul]; refine Dyad.sum _ (fun a ha'=>?_) hδ
     have hi':i≤j:=by simpa [Nat.lt_succ_iff] using hi -- ha' comma
     have he:a≤e:=by simpa [Nat.lt_succ_iff] using ha'
     by_cases hh:a=e
     · subst hh; rw [tsub_self,(Steam.live hv _).dark,(Steam.live hv' _).dark]
       change Dyad _ _ _ _ _ (shift _ _ 0 _) (shift _ _ 0 _)
       rw [cold_r,cold_r]; exact (Dyad.zero hδ).mono (mul_nonneg ((hM c i a).nn hW) hU) -- subst e or a?
     have hy:= HQ i a (c+1) A L h d δ W U V V' Γ Γ' F F' hf hv hv' hΓ hδ hW hU (fun a' r ht=> hG a' r (by unfold taps at *;omega)) (fun a' r ht=>ha a' r (by unfold across at *;omega))
     rw [min_eq_left hi'] at hy
     have hx:= HR i (e-a) (n-c+1) A σ δ W V V' Γ Γ' hv hv' hΓ hδ hW (fun a' r ht=> hG a' r (by unfold taps at *;omega))
     convert click (n:=n) hf hΓ hy hx using 1;unfold M; ring
end YM.RG08.Skiff
