import YM.RG08.Door.Cash
/-!
# BOTH cutoff mark rate in wings. No limit yet. Post-block only for strict events;
no assumption about convergence of witnesses.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
noncomputable section
namespace YM.RG08.Door
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Staffer Reflect UVExt.Paths Work.F08 Push.AbsoluteSums
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels
open scoped BigOperators Topology Real
variable {X:Chain}{G:Gauge}{E e r d τ D j t i k m l n s :ℕ}{R θ C w:ℝ}{F:Labels.Frame G d}{Ω:SectionData F}{ν:G.ColorIndex}{D':ChartRatio G}{H:Hol G}{P:KPrices X.kernel}{g:KGate P}{Q:Lending G X.kernel}{S:Prism G X.kernel g Q E}
variable {h:1/2≤R}{hD:d+1≤D} {T:Signals P Q E τ H Ω h hD}
open Wings
variable {I:Type}{u:I→Windows}
section
variable {A B:ReadsU F D R}{M N:Session (Letter F)}
lemma slate_minus (he:Boards A)(hp:Boards B) : Boards (A-B) := by
  refine ⟨fun b=> ?_,fun b=>?_⟩
  · rw [Pi.sub_apply,sub_eq_add_neg,← neg_one_smul ℝ]; exact choir_plus (he.rank b) (choir_weight (hp.rank b) _)
  rw [Pi.sub_apply,sub_eq_add_neg,← neg_one_smul ℝ]; exact lank_add (he.paid b) (lank_wt (hp.paid b) _)
lemma atlas_sub (H:Hol G)(he:Boards A)(hp:Boards B): atlas H (A-B)= atlas H A-atlas H B:= by
  ext i j k
  rw [Matrix.sub_apply]; change hot (atlas H (A-B)) k i j= PowerSeries.coeff k ((atlas H A i j)-(atlas H B i j)); rw [map_sub]; simp_rw [←hot_node,atlas_fees]
  rw [Pi.sub_apply]; exact congr_fun (congr_fun (audit_sub H (he.rank j) (hp.rank j) (he.paid j) (hp.paid j)) k) i
lemma slack (h:Genuine H A)(hp:Genuine H B)(b: Letter F): auditT H F ((A-B) b)=0:= by ext i j; rw [← atlas_fees,atlas_sub H h.toBoards hp.toBoards,h.cost,hp.cost,sub_self]; rw [hot_node,Matrix.zero_apply,map_zero]; rfl
lemma pamphlet : bureau A M - bureau B N= bureau (A-B) M + bureau B (M-N) := by
  ext1 i; ext1 j; ext1 k
  rw [Pi.sub_apply, Pi.sub_apply,Pi.sub_apply, Pi.add_apply,Pi.add_apply,Pi.add_apply]
  simp_rw [expose, ← sum_sub_distrib,←sum_add_distrib]; refine sum_congr rfl fun v _=>?_ 
  refine sum_congr rfl fun p hp=>?_ ; simp only [realm,Pi.sub_apply,hot_node,Matrix.sub_apply,map_sub,smul_sub]
  have H (x y:ℝ)(b v:EnvelopeU D R G k): x • b-y • v=x • b-x • v+(x-y) • v := by rw [_root_.sub_smul x y v]; abel
  exact H (hot M p v i) (hot N p v i) _ _
end
variable (he:Tights T S ν D' u)
include he
local notation "Ⓨ" => menu X
local notation "Δ" => chop (u:=u) X (1/4)
local notation "Γ" => heights (u:=u) X ν D'
local notation "S♭" => basinT (u:=u) T ν D'
local notation "Ξ" => Xe (u:=u) T ν D'
local notation "T♭" => Te (u:=u) T ν D'
local notation "Υ" => Ye (u:=u) X ν D' T
local notation "Φ" => (Υ-(fun t: Wings u 0=> Υ t.wingR))
local notation "Ψ" => (Ξ-(fun t:Wings u 1=> Ξ t.wingR))
local notation "Θ" => (T♭ -(fun t:Wings u 1=> T♭ t.wingR))
variable {b: Letter F}
lemma cashUp (b: Letter F)(hk:e≤E)(r:ℕ): Tin (menu X) 1 (fun i:Wings u 1=> Υ i.up b e r) (fun i=> ώ T (i.i+1)) := by
  have ht:= cashIn he hk b r; rw [← a_zero X (u:=u)] at ht;
  simpa only [a_zero] using ht.lapP he.hc.M.crop (by norm_num)
lemma tacked (hk:e≤E)(b:Letter F)(hp : Tin (menu X) (chop X (1/4)) (fun i=> Φ i b e r) (fun i=> ώ T i.i)) : Twill (menu X) Δ (fun i:Wings u 1=> Υ i.up b e r) (fun i:Wings u 1=> Υ i.wingR.up b e r) (fun i=>ώ T (i.i+1)) :=
  ⟨cashUp he b hk r,(cashUp he b hk r).move Wings.wingR,hp.lapP he.hc.M.crop (by norm_num)⟩
lemma kilt (hk:e≤E)(hx:∀ j l r',dag e (slot b) r j l r'→ Cage T (1/4) Φ Ψ Θ j l r') :
    Tin Ⓨ Δ (fun i=>fetchU (Γ i) (slot b) d (Υ i.up b) e r-fetchU (Γ i.wingR) (slot b) d (Υ i.wingR.up b) e r) (fun i=> ώ T i.i) := by
  refine (forms_bucks he.operator ((slot_le _).trans he.hh) hk (fun i=>(he.firs (i:Wings u 1).up).rank b) (fun i=> (he.firs (i:Wings u 1).wingR.up).rank b) h ?_).goes
  intro j k hp; have hh:= below (l:=slot b) hp
  exact tacked he (by unfold dag at hh; omega) b ((hx j (slot b) k hh).first b rfl)
lemma chorus : Rails (1/4) T Φ Ψ (fun i=> Υ i.wingR.low) T♭ Θ := by
  have hχ (i: Wings u 0) : Boards (Φ i) := slate_minus (he.firs i).toBoards (he.firs _).toBoards
  refine {bound:=he.hh,small:=le_refl _,lam:=hχ,wave:=fun i=>slate_minus (he.lived i) (he.lived _),eve:=fun i=>(he.firs _).toBoards,nullL:=fun i b=> slack (he.firs i) (he.firs _) _,shine:=fun i=>(he.reads i).1,inverse:=he.prior,pruner:=fun i=> (atlas_sub H (he.lived i) (he.lived _)).symm,pay:=?_,fuel:=fun e he' b r=> (cashIn he he' b r).move (fun i:Wings u 1=> i.wingR.low), switch:=fun e v b hr _=> stakesPay he hr b v,stage:=?_,top:=?_,upgrade:=?_}
  · intro i; change Ξ i- Ξ i.wingR=_; rw [(he.reads i).2,(he.reads i.wingR).2]; exact pamphlet
  · intro e hp b r; have ht:= cashIn he hp b r
    exact (ht.move Wings.roof).less (ht.move (fun i:Wings u 0=> i.roof.wingR)) (fun i=>sh X _)
  · intro e b r hk hm hp; let D (i:Wings u 1):= fetchU (Γ i) (slot b) d (Υ i.up b) e r; let Du i:= D (Wings.wingR i); have hD:Tin Ⓨ Δ (D-Du) (fun i=>ώ T i.i):= kilt he hk hp -- Du shadow
    let U i:= Φ (Wings.up i) b
    have ht := he.walkPays (fun i=>(hχ (i:Wings u 1).up).rank b) (r:=r) (by have h:(slot b) ≤ τ:=(slot_le _).trans he.hh; omega) hm (fun j hj k=> ((hp j (slot b) k (Or.inl hj)).first b rfl).lapP he.hc.M.crop (by norm_num)) -- theta implicit
    let V i:= aboard d (Γ i).tree (U i e r)-aboard d (babyQ G X i) (U i e r)
    have H(i:Wings u 1): Ξ i b e r=aboard d (Γ i).tree (Υ i.up b e r)+D i := formula_bucks (he.fair i) ((he.firs _).rank b) h _ _ _
    let f (i:Wings u 1) := Υ i.wingR.up b; let A (i:Wings u 1):= aboard d (Γ i).tree (f i e r)-aboard d (Γ i.wingR).tree (f i e r)
    have hA : Tin Ⓨ Δ A (fun i=> ώ T i.i):= (aboard_bucks he.operator (fun i=>(he.firs _).rank b) (fun i=>(he.firs _).rank b) (U:=f) (V:=f) h (Twill.same ((cashUp he b hk r).move Wings.wingR))).goes
    rw [show (fun i=> _-aboard d (babyQ G X i) ((Φ (Wings.up i)) b e r))= A+(V+(D-Du)) from funext fun i=>?_]; · exact hA.plus (ht.plus hD (sh X)) (sh X)
    have he' := Needle.aboard_sub (X.S.block_odd _) h (he.fair i|>.ct) ((he.firs i.up).rank b|>.hem e r) ((he.firs i.wingR.up).rank b|>.hem e r) d
    have hp: U i e r= Υ i.up b e r- f i e r:= rfl
    change Ξ i b e r-Ξ i.wingR b e r- aboard d (babyQ G X i) (U i e r)= A i+(V i+(D i-Du i))
    unfold A V; rw [hp]; unfold f Du; rw [he',H i,H i.wingR]; abel
  intro e b r hk hn hp hh
  let D (i:Wings u 1):= fetchU (Γ i) (slot b) d (Υ i.up b) e r; let A i:= aboard d (Γ i).tree (Υ i.up b e r)
  have H(i:Wings u 1): Ξ i b e r=A i+D i:= formula_bucks (he.fair i) ((he.firs _).rank b) h _ _ _
  have hx := (aboard_bucks he.operator (fun i=> (he.firs i.up).rank b) (fun i=>(he.firs i.wingR.up).rank b) h (tacked he hk b hh) (d:=d)).goes
  rw [show (fun i=> Ψ i b e r)=(A-fun i=>A i.wingR)+ (fun i=> D i-D i.wingR) from funext fun i=>?_]; · exact hx.plus (kilt he hk hp) (sh X)
  simp only [Pi.add_apply, Pi.sub_apply,H]; abel
end YM.RG08.Door
