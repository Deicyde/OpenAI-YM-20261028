import YM.TraceExtension.Perfect.Nibble

/-! # Ticket to generic contracting jets. Use eventual admissible residual (uniform per m) accounting. -/
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Perfect
open Function Filter Matrix Lattice Precision Laurent Stationary Bloch Exterior Tree RG Wilson Finset Planned.PrimaryIntegral295 Next.Free Asymptotics RowGrade
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {W:Type}{F:Filter W}

def earns (F:Filter W)(g:W→ℝ)(c:ℝ):Prop := ∀ ε:ℝ,0<ε→∀ᶠ w in F,g w ≤ c+ε

namespace earns
variable {g f:W→ℝ} {a b:ℝ}
lemma eventually (h:∀ᶠ i in F,f i ≤ a): earns F f a:=fun _ he=>h.mono (fun i h=> by linarith)
lemma tendsto (h:Tendsto f F (𝓝 a)): earns F f a := fun _ he => h.eventually (ge_mem_nhds (by linarith))
lemma tighten (h:earns F f a)(hp:∀ᶠ i in F,g i≤f i): earns F g a:=fun ε he=> by filter_upwards [h ε he,hp] with i hi hx; exact hx.trans hi
lemma higher (h:earns F f a)(he:a≤b): earns F f b:=fun ε hp=> by filter_upwards [h ε hp] with i hh; linarith
lemma add (h:earns F f a) (g':earns F g b): earns F (fun i=>f i+g i) (a+b) :=fun ε he=> by filter_upwards [h (ε/2) (half_pos he),g' (ε/2) (half_pos he)] with i h hh; linarith only[h,hh]
lemma sum {V:Type} (P: Finset V)(f:V→W→ℝ)(Z:V→ℝ)(ht:∀ i∈P,earns F (f i) (Z i)) : earns F (fun w=> ∑ i∈P,f i w) (∑ i∈P,Z i):=by
 induction P using Finset.induction with
 | empty=> exact eventually (Eventually.of_forall fun i=> by simp)
 | insert a l hl ih=> simp_rw [sum_insert hl]; exact (ht a (mem_insert_self ..)).add (ih (fun i h=> ht i (mem_insert_of_mem h)))
lemma unit {q:ℝ}(hp:0 ≤ q)(h:earns F f a): earns F (fun w=>q*f w) (q*a) :=fun ε he=>by
 rcases eq_or_lt_of_le hp with hQ|hQ; · exact Eventually.of_forall fun i => by change q*f i≤q*a+ε; rw [← hQ]; simp [he.le]
 filter_upwards [h (ε/q) (div_pos he hQ)] with w hw; exact (mul_le_mul_of_nonneg_left hw hp).trans_eq (by field_simp)
end earns
variable {I J:Type} [Fintype I] [DecidableEq I][Fintype J][DecidableEq J]{α β σ ρ T C :ℝ}{t b:ℕ}{p:Rays I→ Rays J}
lemma ferries_head (B:I→ℕ)(t:ℕ)(r:Rays I)(v:Rays J→ℝ)(A:J→ I→ℝ)(h:∀ x y,fderiv ℝ p r (desk y) x = A x y) :
    ferries B α t v p r (.atomic 2)= cost B α t 0 (bisect A A (iteratedFDeriv ℝ 2 v (p r))):=by
    unfold ferries
    congr 1; ext1 i; rw [name_bisect,Cases.one]; congr 1; ext1 j;ext1 k;fin_cases j <;> exact h _ _

lemma young_r (S:ℝ)(t:ℕ) (R:I→ℕ)(v:Rays I) (G:Rays J→ℝ)(hp:ContDiffAt ℝ ω p v)(h:ContDiffAt ℝ ω G (p v))(he:fderiv ℝ G (p v)=0):
    cost R S t 0 (leaf (G ∘ p) v 2) ≤ ferries R S t G p v (.atomic 2):=by
  apply (split_fees G p v h hp 2).trans; rw [sum_eq_single (.atomic 2)]
  · intro i _ hi; unfold ferries cost; apply Finset.sum_eq_zero; intro v₀ _; unfold Cases.caseRead
    have hℓ : i.length = 1 := by have ht:=i.length_pos (by decide); have hh:=i.length_le; have he:i.length≠2:=fun h=> hi (Cases.finest _ h); omega
    have hg: iteratedFDeriv ℝ i.length G (p v)=0:=by
       ext1 x; revert x; rw [hℓ]; intro x; rw [iteratedFDeriv_one_apply,he]; rfl
    rw [hg]; simp
  simp

variable {c f: W→Side}{G:Gauge}

variable (g:∀ w,StepData (c w) (f w)) (P:∀ w,CrossA (g w).ratio.count)(U:∀ w,Acr G (c w)→Acr G (f w))(o:∀ w,Site (f w))(v:∀ w,Site (c w))(L:Side)
set_option quotPrecheck false
local notation "W!"=> fun w (z:pairA G (f w))(i:pairA G (c w))=> fderiv ℝ (U w) 0 (desk i) z
local notation "p!"=>fun w=> amber (g w) (P w) (o w) (G:=G)
local notation "q!"=>fun w=> aquifer (g w) (P w) (o w) (G:=G)
local notation "u"=> (L.val:ℝ)
variable (A:∀ w,Acr G (f w)→ℝ) (hA:∀ w,ContDiffAt ℝ ω (A w) 0)(hU:∀ w,ContDiffAt ℝ ω (U w) 0) (hx:∀ w,U w 0=0)(hf:∀ w,fderiv ℝ (A w) 0=0)
local notation "ct"=> fun w=>landW (G:=G)  (o w)
local notation "cf"=>fun w=>landW (G:=G) (v w)
local notation "wc"=> α
local notation "M!"=>fun w=>iteratedFDeriv ℝ 2 (A w) 0
variable {V: ℝ}{a:ℕ} (hp:0 ≤ V)(hk:∀ᶠ w in F,Settle (landW (v w)) (landW (o w)) (fun z i=> fderiv ℝ (U w) 0 (desk i) z) (amber (g w) (P w) (o w)) (aquifer (g w) (P w) (o w)) α a (L.val:ℝ) V)
local notation "S!" => a
local notation "Z!"=> F
include hp hk
set_option maxRecDepth 6000 in
set_option maxHeartbeats 800000 in
lemma lot_amber (h:Stoke F o A 0 4)(he:0≤α)(hz: ∀ᶠ w in F,11≤ (f w).val):
     earns F (fun w=> cost (cf w) α a 0 (bisect (p! w) (p! w) (M! w))) 0:=by
    have hy:∀ᶠ w in F,∀ i:Ore G, sh (cf w) α a 0 (carnel (g w) (P w) (o w) i) ≤ 2*V:=by
        refine (hk.and hz).mono (fun w H=>?_); obtain ⟨hx,hZ⟩:=H
        exact (economize (g w) (P w) (o w) he hx hZ (by exact_mod_cast L.property) hp).1
    apply earns.tendsto; exact table_lotto _ _ _ _ (fun w=> fun i:Ore G=>meshOre i (o w)) _ (fun w=>carnel (g w) (P w) (o w)) _ (fun i x=> surface ..) (fun i x=> surface ..) he (by positivity) (by positivity) hy hy (fun i j=> earth_acts _ _ _ h i j)
lemma lot_quartz (h:Stoke F o A 0 5)(he:0≤α)(hz: ∀ᶠ w in F,11≤ (f w).val):
     earns F (fun w=> cost (cf w) α a 0 (bisect (p! w) (q! w) (M! w)+bisect (q! w) (p! w) (M! w))) 0:=by
    have hy:∀ᶠ w in F,(∀ i:Ore G, sh (cf w) α a 0 (carnel (g w) (P w) (o w) i) ≤ 2*V) ∧ ∀ i:Bar G, sh (cf w) α a 0 (lagoon (g w) (P w) (o w) i) ≤ 9*V:=by filter_upwards [hk,hz] with w h hw using economize (g w) (P w) (o w) he h hw (by exact_mod_cast L.property) hp
    let p(w):= fun v:Ore G=> meshOre v (o w); let q(w):= fun v:Bar G=>meshBar v (o w)
    let C w:= carnel (g w) (P w) (o w) (G:=G);let D(w):= lagoon (g w) (P w) (o w) (G:=G)
    have hx:= earns.tendsto (table_lotto (cf) (M!) (p!) (q!) p q C D (fun i x=> surface ..) (fun i x=>waters ..) he (by positivity) (by positivity) (hy.mono (fun i h=> h.1)) (hy.mono (fun i h=>h.2)) (fun i j=>wind_acts f A o h i j true))
    have hp:= earns.tendsto (table_lotto (cf) (M!) (q!) (p!) q p D C (fun i x=> waters ..) (fun i x=>surface ..) he (by positivity) (by positivity) (hy.mono (fun i h=> h.2)) (hy.mono (fun i h=>h.1)) (fun i j=>wind_acts f A o h j i false))
    have he:= (hx.add hp).tighten (Eventually.of_forall fun w=> cost_add (cf w) α a 0 (bisect (p! w) (q! w) (M! w)) (bisect (q! w) (p! w) (M! w)))
    rw [zero_add] at he; exact he
include hA hf hU hx
lemma billed_near (h:Stoke F o A 0 4)(he:0 ≤ α)(ht:4≤ a)(hz: ∀ᶠ w in F,11 ≤ (f w).val)(hg: α/(L.val:ℝ) ≤ β)(M:ℝ)(hr:earns F (fun w=> cost (ct w) β a 0 (leaf (A w) 0 2)) M):
    earns F (fun w=> cost (cf w) α a 0 (leaf (A w ∘ U w) 0 2)) (((2:ℝ)^(a+9)*V^2/(L.val:ℝ)^5)*M):=by
    let s:ℝ:= 2^(a+9)*V^2/(L.val:ℝ)^5
    have hh:= (hr.unit (q:=s) (by unfold s; positivity)).add (lot_amber g P U o v L A hp hk h he hz)
    rw [add_zero] at hh; refine hh.tighten ?_; filter_upwards [hk] with w hg'
    apply (young_r α a (cf w) 0 _ (hU w) (hx w |>.symm ▸ hA w) (hx w|>.symm ▸ hf w)).trans
    rw [ferries_head _ _ _ _ (W! w) (fun _ _=>rfl),hx]; exact reflection_near hg' (M! w) (by exact_mod_cast L.property) hp he hg ht
lemma billed_after (h:Stoke F o A 0 5)(he:0 ≤ α)(ht:4≤a)(hz:∀ᶠ w in F,11 ≤ (f w).val)(hg:α/(L.val:ℝ) ≤ β)(M:ℝ)(hr:earns F (fun w=>cost (ct w) β a 0 (leaf (A w) 0 2)) M) :
    earns F (fun w=> cost (cf w) α a 0 (leaf (A w ∘ U w) 0 2)) (((2:ℝ)^(a+8)*V^2/(L.val:ℝ)^6)*M):=by
    let s:ℝ:=2^(a+8)*V^2/(L.val:ℝ)^6
    have hV:Stoke F o A 0 4:=⟨fun i j hy=>h.taste _ _ (by omega)⟩
    have hh:= (hr.unit (q:=s) (by unfold s; positivity)).add ((lot_amber g P U o v L A hp hk hV he hz).add (lot_quartz g P U o v L A hp hk h he hz))
    rw [add_zero,add_zero] at hh; refine hh.tighten ?_; filter_upwards [hk] with w hg'
    apply (young_r α a (cf w) 0 _ (hU w) (hx w|>.symm ▸ hA w) (hx w|>.symm ▸ hf w)).trans
    rw [ferries_head _ _ _ _ (W! w) (fun _ _=>rfl),hx]; exact reflection hg' (M! w) (by exact_mod_cast L.property) hp he hg ht

lemma billed_all (hC:0 ≤ C)(he:0 ≤ α)(ht:b ≤ a)(hℓ:2≤ b)(hg:α/(L.val:ℝ) ≤ β)(hw:∀ᶠ w in F,∀ i j,j≤b → sail (U w) 0 (cf w) j i α a (landW (o w) i/(L.val:ℝ)) ≤ C)(Dπ:ℕ→ℝ)(hD:∀ i, 0 ≤ Dπ i)(hr:∀ i,i ≤ b→2 ≤ i→ earns F (fun w=>cost (ct w) β a 0 (leaf (A w) 0 i)) (Dπ i)) :
   earns F (fun w=>cost (cf w) α a 0 (leaf (A w ∘ U w) 0 b))
       ((V*2/(L.val:ℝ)^2)^b*Dπ b+ ∑ i∈univ.erase (OrderedFinpartition.atomic b), C^i.length*Dπ i.length):=by
    let s w c:= ferries (cf w) α a (A w) (U w) 0 (c: OrderedFinpartition b)
    let i:= OrderedFinpartition.atomic b
    have hp' : 1 ≤ (L.val:ℝ):= by exact_mod_cast L.property
    have hA' : earns F (fun w=> s w i) ((V*2/(L.val:ℝ)^2)^b*Dπ b):=by
        refine ((hr b le_rfl hℓ).unit (q:=(V*2/(L.val:ℝ)^2)^b) (by positivity)).tighten ?_; filter_upwards [hk] with w hv
        have hh := fee_atomic (x:=0) (g:=A w) (f:=U w) hp' he hg ht (S:=V) hp (A:=cf w) (B:=ct w) (fun j=> ?_); rotate_left
        · rw [mono_sail]; exact hv.total j
        rw [hx] at hh; exact hh
    have hZ j (hj:j∈ univ.erase i) : earns F (fun w=> s w j) (C^j.length * Dπ j.length):=by
        by_cases hp:2≤ j.length
        · have he:=hr j.length j.length_le hp; refine (he.unit (q:= C^j.length) (by positivity)).tighten ?_
          filter_upwards [hw] with w h; unfold s; have hx' := fee_coarse (g:=A w) (x:=0) (A:=cf w) (B:=ct w) (f:=U w) j hp' (show 0≤α from ‹0≤α›) hg (fun _=>C) (fun i j'=> h j' _ (j.partSize_le i)); simp only [Finset.prod_const,Fintype.card_fin,Finset.card_univ,hx] at hx';exact hx'
        refine earns.eventually (Eventually.of_forall fun w=> ?_); unfold s ferries cost; rw [Finset.sum_eq_zero]; exact mul_nonneg (pow_nonneg hC _) (hD _)
        intro p _; unfold Cases.caseRead; have ht :j.length=1:=by have h:= j.length_pos (by omega); omega
        have he : iteratedFDeriv ℝ j.length (A w) 0=0:=by ext1 m; revert m; rw [ht]; intro m; rw [iteratedFDeriv_one_apply,hf w]; rfl
        rw [hx,he]; simp
    refine (hA'.add (earns.sum (univ.erase i) (fun j w=> s w j) _ hZ)).tighten (Eventually.of_forall fun w=>?_)
    refine (split_fees (A w) (U w) 0 (by rw [hx];exact hA w) (hU w) b).trans ?_; change (∑ i,s w i) ≤ _; exact (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm.le
end YM.Trace.Perfect
