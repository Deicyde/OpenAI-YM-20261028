import YM.RG08.Door.Tuba
/-!
# Local ticket recurrence SOLVED on all orders on admitted mesh.
Abstract: expansion ledgers (Mark `awaits`) above at earlier ranks. No assumption on repeated rule.
Propagate Variation against a baseline with `pull` and `hot` data, plus IV price already available for SAME-event operator split. `AvailF` filled twice in sequence: absence of companion, comparison.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
noncomputable section
namespace YM.RG08.Door
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Staffer Reflect UVExt.Paths Work.F08 Push.AbsoluteSums
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels
open scoped BigOperators Topology Real
variable {X:Chain} {G:Gauge}{E e r d τ D j t i k m l n s :ℕ}{R θ C w:ℝ}{F:Labels.Frame G d}{Ω:SectionData F}{ν:G.ColorIndex}{D':ChartRatio G}{H:Hol G}{P:KPrices X.kernel}{g:KGate P}{Q:Lending G X.kernel}{S:Prism G X.kernel g Q E}
variable {h:1/2≤R}{hD:d+1≤D} {T:Signals P Q E τ H Ω h hD}
open Wings
variable {I:Type}{u:I→Windows}
local notation "Ⓨ" => menu (u:=u) X
local notation "Δ" => chop (u:=u) X
local notation "Φ" => Wings u 0→ReadsU F D R
local notation "Υ" => Wings u 1→ReadsU F D R
local notation "℧" => Wings u 1→ Session (Letter F)

structure Cage (T:Signals P Q E τ H Ω h hD)(θ:ℝ)(V:Φ)(U:Υ)(T':℧)(e l r:ℕ) : Prop where
  first b: slot b=l → Tin (menu X) (chop X θ) (fun i:Wings u 0=> V i b e r) (fun i=>ώ T i.i)
  second b: slot b=l → Tin (menu X) (chop X θ) (fun i:Wings u 1=> U i b e r) (fun i=>ώ T i.i)
  knows b: slot b=l→∀ v,slot v=r→ Dig (menu X) (chop X θ) (fun i=> hot (T' i) e v b)
variable {M W: Wings u 0 →ReadsU F D R}{U V A: Wings u 1→ ReadsU F D R}{R' T': Wings u 1→Session (Letter F)}

structure Rails (θ:ℝ)(T:Signals P Q E τ H Ω h hD)(M:Φ)(U A:Υ)(R' T':℧): Prop where
  bound : d≤τ
  small : θ ≤ 1/4
  lam i : Boards (M i)
  wave i : Boards (U i)
  eve i : Boards (A i)
  nullL i b: auditT H F (M i b)=0
  pruner i : T' i=atlas H (U i)
  pay i : U i=bureau (M i.low) (R' i)+bureau (A i) (T' i)
  shine i : Flash (X.S.block i.i) (R' i)
  inverse i a b : ‖singSl (R' i)⁻¹ a b‖ ≤ price_u T i.toLaunch
  fuel e (he:e≤E) b r : Tin (menu X) 1 (fun i:Wings u 1=> A i b e r) (fun i=>ώ T i.i)
  switch e i b : e≤E→ Dig (menu X) (chop X θ) (fun v=> hot (T' v) e i b) → Dig (menu X) 1 (fun v=>hot (R' v) e i b)
  top (e : ℕ) : e≤ E→ ∀ b r,Tin (fun i:Wings u 0=>menu X i.roof) 1 (fun i:Wings u 0=> M i.roof b e r) (fun i=>ώ T i.roof.i)
  stage e b r : e≤E → r≤slot b + e → (∀ j n s,dag e (slot b) r j n s → Cage T θ M U T' j n s) →
     Tin (menu X) (chop X θ) (fun i=> U i b e r-aboard d (babyQ G X i) (M (Wings.up i) b e r)) (fun i=>ώ T i.i)
  upgrade e b r : e≤E→ r≤ slot b+e → (∀ j n s,dag e (slot b) r j n s→ Cage T θ M U T' j n s) →
     Tin (menu X) (chop X θ) (fun i=> M i b e r) (fun i:Wings u 0=>ώ T i.i) → Tin (menu X) (chop X θ) (fun i=> U i b e r) (fun i:Wings u 1=>ώ T i.i)

private lemma empty_cage (hR:Rails θ T M U A R' T') (hn : l+e< r) : Cage T θ M U T' e l r := by
  have hM(t) b (hz:slot b=l): M t b e r=0:= not_ne_iff.mp (mt (((hR.lam t).rank b).cap e r) (by omega))
  have hU(t) b (hz:slot b=l): U t b e r=0:= not_ne_iff.mp (mt (((hR.wave t).rank b).cap e r) (by omega))
  refine ⟨fun b hb=>?_,fun b hb=>?_,fun b hb v hv=>?_⟩
  · simp_rw [fun t=> hM t b hb]; exact Tin.zero
  · simp_rw [fun t=> hU t b hb]; exact Tin.zero
  simp_rw [fun t=> hR.pruner t, atlas_fees, fun t=> audit_cap H (((hR.wave t).rank b).cap) v (by omega:e+slot b<slot v)]; exact Dig.zero
private lemma close_cage (h:Enabled T u)(hR:Rails θ T M U A R' T') (he:e≤E) (hb:l ≤ d)(hx : ∀ j n s,dag e l r j n s → Cage T θ M U T' j n s) : Cage T θ M U T' e l r := by
  by_cases hr : r≤l+e
  swap; · exact empty_cage hR (by omega)
  have H' (b:Letter F) (ht:slot b=l) := hR.stage e b r he (by omega) (ht.symm ▸ hx)
  have hv (b:Letter F) (ht:slot b=l) (v:Letter F) (hs:slot v=r) : Dig (menu X) (chop X θ) (fun t=> hot (T' t) e v b) := by
    simp_rw [hR.pruner]; refine siphon (U:=fun i=> M i.up) h (fun i=>hR.lam _) (fun t=> hR.nullL _ b) (fun t=>hR.wave t) (fun j hj r=> (hx j _ r (Or.inl hj)).second b ht) (H' b ht) v hs
  have hu(b:Letter F)(ht:slot b=l) j v (hp: dag e (slot b) r j (slot b) (slot v) ∨ (j=e∧ slot v=r)) : Dig (menu X) (chop X θ) (fun t=> hot (T' t) j v b) := by
    rcases hp with h|⟨h,hv'⟩
    · exact (hx j _ _ (ht ▸ h)).knows b rfl v rfl -- slot
    subst j; exact hv _ ht _ hv'
  have hc b (ht:slot b=l): Tin (menu X) (chop X θ) (fun i=> M i b e r) (fun i:Wings u 0=>ώ T i.i) := by
    apply transferSl (V:=fun i b=> M i b e r) hR.small h hR.shine hR.inverse (show r≤τ+E by have hh:=hR.bound; omega) (fun i b=>held H ((hR.lam i).rank _) ((hR.lam i).paid _) (hR.nullL i b) e r) (fun i b=> (hR.lam i).paid _ _ _) (l:=l) (fun b hb=>hR.top e he _ _) ?_ _ ht
    intro b hu'
    let k i:= palms (R' i) (M (Wings.low i)) e r b
    have hO j v (hp:dag e (slot b) r j (slot b) (slot v) ∨ j=e ∧slot v=r) := hR.switch j v b (by unfold dag at hp; omega) (hu b hu' j v hp)
    have hK : Tin (menu X) (chop X θ) k (fun i:Wings u 1=>ώ T i.i):= ferns (sh X) b (fun i=>(hR.shine i).toDilation) (fun i=>hR.lam i.low) (fun j p i ha=> ((hx j _ i (by rw [hu'] at ha; exact ha)).first p rfl).move Wings.low) hO -- type transfer vinyl
    have ht:= views (X:=A) (sh X) b hR.eve (fun k hk'=>hR.fuel k (hk'.trans he)) (hu b hu')
    let D i:= U i b e r - aboard d (babyQ G X i) (M i.up b e r)
    rw [show (fun i=> footnote _ _ _ _ - _)= D-k-fun i=>bureau (A i) (T' i) b e r from funext fun i=>?_]
    · exact ((H' b hu').less hK (sh X)).less ht (sh X)
    simp only [k,D,Pi.sub_apply]; rw [hR.pay]; simp only [Pi.add_apply,exposure (W:=R' i)]; abel
  exact ⟨hc,fun i hi=> hR.upgrade _ i r he (by omega) (by rw [hi]; exact hx) (hc _ hi),hv⟩
lemma railway (ht:Rails θ T M U A R' T')(he:Enabled T u) (hp:e≤E) (l r:ℕ): Cage T θ M U T' e l r := by
  induction e using Nat.strong_induction_on generalizing l r with
  | h e ih=>
    induction l using Nat.strong_induction_on generalizing r with
    | h l H' =>
      by_cases h:l ≤ d
      swap
      · have he (b:Letter F)(hb:slot b=l):False:= h (hb ▸ slot_le b); exact ⟨fun b hb=>(he b hb).elim,fun b hb=>(he b hb).elim,fun b hb=>(he b hb).elim⟩
      by_cases hh:r≤l+e
      swap; · exact empty_cage ht (by omega)
      generalize hL : l+e-r=y; induction y using Nat.strong_induction_on generalizing r with
      | h y hy=>
         refine close_cage he ht hp h fun j n s h'=> ?_
         rcases h' with Hv | ⟨hj,hq|⟨hk,hB⟩⟩
         · exact ih _ Hv (Hv.le.trans hp) n s
         · subst j; exact H' n hq s
         subst n j; by_cases hk:s≤l+e
         · exact hy _ (by omega) s hk rfl
         exact empty_cage ht (by omega)
end YM.RG08.Door
