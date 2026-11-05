import YM.RG08.Creek.Treaty
/-! # Sphere cost solved UV. Arbitrary root source sequence if coherent and fees polynomial y^p AFTER arbitrary amplitude external; requires separation demand explicitly prior to cut N. -/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.RG08.Creek
open Function Finset Filter RG Lattice Laurent Quire Vale Bloch Next.Free Stationary Shade Wax Town Bands Plot Needle Tall Scores Push.AbsoluteSums Work.F08 Door
open Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset RG Bloch Conductor Staffer Reflect UVExt.Paths Planned.PrimaryIntegral295 Place Source Source.Drops Labels Summit Wings High
open scoped Topology ContDiff BigOperators Real Classical Matrix
variable {X:Chain} {G:Gauge}{E e r d τ D j t f i k m n :ℕ}{R θ C w ρ χ:ℝ}{F:Labels.Frame G d}{Ω:SectionData F}{ν:G.ColorIndex}{D':ChartRatio G}{H:Hol G}
variable {P:KPrices X.kernel}{g:KGate P}{Q:Lending G X.kernel}{S:Prism G X.kernel g Q E}
variable {h:1/2≤R}{hD:d+1 ≤ D}{T:Signals P Q E τ H Ω h hD}
variable {I J Y:Type} [Fintype I][DecidableEq I]{u:Y→Windows}{a b:I→ℕ}{B: ℕ→ Side}{Z:ℕ→ℝ}
section prime
-- multiplicative reward by marks; allows joins at equal grade *without* charging nonlinear power on prior bound

def boon (ρ:ℝ)(p:I→ℝ)(t:Finset I):= ρ^t.card*∏ i∈t,p i
lemma boon_pos (a:I→ℝ)(h:0≤a)(p:ℝ)(hp:0≤p): Crease (boon p a):= by
   refine ⟨fun t=>mul_nonneg (by positivity) (prod_nonneg fun _ _=>h _),fun i a he=> le_of_eq ?_⟩; obtain ⟨rfl,hv⟩:= (norms_par _ _).mp he; unfold boon; rw [prod_union hv,card_union_of_disjoint hv,pow_add,mul_mul_mul_comm]
variable {F:Layouts I G D R}{P': Wax.Head I}
def Chief (V: Verts I)(ρ:ℝ)(P:Wax.Head I)(A:Layouts I G D R) (w:ℝ)(E:ℕ):Prop:=∀ t:Finset I,∀ i≤ E,∀ k, Owns w t (fun x:Places I=>rift V A x t i k) ((if 1 < t.card then Real.exp (-ρ) else 1)*P t)
lemma ch_fest {V:Verts I} (h:Chief V ρ P' F w E)(hv:Crease P')(he : 0≤ρ): Fest w E 1 P' (rift V F):= by
   intro i hi k t; apply owns_mono (h t i hi k) le_rfl; split; exact mul_le_mul_of_nonneg_right (Real.exp_le_one_iff.mpr (neg_nonpos.mpr he)) (hv.pos _); exact le_rfl
end prime
variable {p:J→ Dial u}
section account
variable {U:J→I→ℕ→BoardU D R G}{A:I→ J→ℝ}
local notation "Ⓒ" => High.glass X (b:=p)
private lemma receipt_b (hp: Attract ν D' X p U a b) (hw: BrookW T u I Z)(hb:Bureau Z E X U p A)(hZ:∀ i,vanes a i+E≤τ)(hA:∀ i,0≤ A i) :
     ∃ H: High p 0→ℝ, Weighed Ⓒ H ∧ (∀ s,1≤H s)∧ ∀ i ≤ E,∀ j s (k:High p 0), Owns (Z (X.J k.i)) {s} (fun x=> markZ (fun i=> U k.z i k.i) x {s} i j) (boon (H k) (fun i=> A i k.z) {s}):=by
    choose V hV Hv using fun (i:Fin (E+1)) (j : Fin (τ+1)) s => (hb i (by omega) s j).serves
    let B(k:High p 0):= ∑ s:I,∑ i, ∑ j,V i j s k; have hB: Weighed Ⓒ B:= weighs_man (glint X p 0) univ fun s (_:s∈(univ:Finset I))=> weighs_man (glint X p 0) (univ:Finset (Fin (E+1))) fun i _=>weighs_man (glint X p 0) (univ:Finset (Fin (τ+1))) fun j _=> hV i j s
    let H:= 1+B; have hh:H ≥ 1:= fun p=>le_add_of_nonneg_right (hB.positive _)
    refine ⟨H,Weighed.one.plus hB (glint X p 0),hh,fun i hi j s v=>?_⟩
    unfold boon; rw [prod_singleton, card_singleton,pow_one]; apply eyes_offer
    by_cases h:j≤τ
    · let z:Fin (E+1):=⟨i,by omega⟩; let p:Fin (τ+1):=⟨j,by omega⟩
      have hr : V z p s v≤ B v:=by
        refine (single_le_sum (s:=univ) (f:=fun j=>V z j s v) (fun j _=>(hV ..).positive v) (mem_univ p)).trans ?_
        exact (single_le_sum (s:=univ) (f:=fun i=>∑ j,V i j s v) (fun i _=>sum_nonneg fun j _=>(hV i j s).positive v) (mem_univ z)).trans (single_le_sum (s:=univ) (f:=fun s=>∑ i,∑ j,V i j s v) (fun s _=> sum_nonneg fun i _=> sum_nonneg fun j _=> (hV ..).positive v) (mem_univ s))
      exact Ink.raise (Hv z p s v) (mul_le_mul_of_nonneg_right (hr.trans (le_add_of_nonneg_left zero_le_one)) (hA _ _))
    rw [not_ne_iff.mp (mt ((hp.leaf v s).cap i j) (by have ht:=hZ ({s}:Finset I); rw [vanes,sum_singleton] at ht; omega))]; exact Ink.raise (Ink.none _ _) (mul_nonneg (zero_le_one.trans (hh v)) (hA _ _))
-- receipt unif. hpb hydrogen budget.
lemma high_tail (hc:Tights T S ν D' u) (hh: Attract ν D' X p U a b)(hw:BrookW T u I Z)(hb:Bureau Z E X U p A)(hZ:∀ i,vanes a i+E≤τ)(hA:∀ i,0≤ A i):
   ∃ (H:High p 0→ℝ)(C:ℝ)(P:ℕ),0 < C ∧ Weighed Ⓒ H∧(∀ i,1≤H i)∧ ∀ i: High p 0,∀ χ ρ:ℝ,0≤χ → C * (Dial.fee X (p i.z))^P*(1+χ)≤ρ → Chief (rural X.S ρ (p i.z).K i.i) χ (boon (H i) (fun t=> A t i.z)) (ownerU X ν D' p U a b i.z i.i) (Z (X.J i.i)) E:= by
   obtain ⟨M,hM,HM⟩:= funds_rift hc hw b
   obtain ⟨H,hH,hL,H'⟩:= receipt_b hh hw hb hZ hA
   have hp (i:High p 1): Climate (heights X ν D' i.appr):=seasonal hc _
   let C i:= M (High.appr (b:=p) i)*(H i.upT)^(Fintype.card I)
   obtain ⟨D,P'',hq,Hq⟩:= harvest_damp (fun i: High p 1=> hw.irrigate (X.J i.i)) (show Weighed (High.glass X) C from (hM.transfer High.appr).times (((age_take hc).sway (glint X p 1) (hH.transfer upT)).powers _)) ((hw.cost.transfer Wings.toLaunch).transfer appr)
   refine ⟨H,D,P'',hq,hH,hL,fun z χ ρ hv hx=>?_⟩
   obtain ⟨s,n,ht,hl⟩:=z; simp only [add_zero] at hl; dsimp only
   let F:= ownerU X ν D' p U a b s; let V:= rural X.S (I:=I) ρ (p s).K; let W(i:High p 0):= boon (H i) (fun t=>A t i.z)
   have ho(i:High p 0): Crease (W i):= boon_pos _ (show 0≤ (fun t:I=>A t i.z) from fun t=>hA _ _) _ (zero_le_one.trans (hL _))
   let K i:= Z (X.J i)
   induction hl using Nat.decreasingInduction with
   | self=>
     let w:High p 0:= ⟨s,(p s).N,ht,le_refl _⟩; let D i:=U s i (p s).N
     intro T i hi j
     change Owns (K (p s).N) _ (fun x=>rift _ (F _) x _ _ _) (_*W w T)
     have hf : F (p s).N=markZ D:= by unfold F ownerU; rw [ledgerR, if_neg (lt_irrefl _)]
     rw [hf]
     by_cases h:T.card=1
     · obtain ⟨y,rfl⟩:=card_eq_one.mp h; rw [card_singleton,if_neg (lt_irrefl _),one_mul]
       exact rift_fe (eyeSense (hh.leaf w)) (rule_w ..) (H' i hi j y w)
     simp_rw [rift,markZ, dif_neg h, ite_self]; refine owns_none T _ (mul_nonneg ?_ (ho w|>.pos _)) _ _ _; split; exact (Real.exp_pos _).le; exact zero_le_one
   | of_succ n hN ih=>
     have he: (p s).K ≤ n+1:= ht.trans (Nat.le_succ _)
     let i: High p 1:= ⟨s,n,ht,hN⟩; have hy:= owned_tv hh hp h i.upT; have hu:= owned_tv hh hp h i.lowT
     change Chief (V n) χ (W i.lowT) (F n) (K n) E
     let F':= rift (V (n+1)) (F (n+1)); have hU: Sense a F':=riftStyle hy.1 (rule_w ..)
     let T':= creekT (heights X ν D' i.appr) a (vaneW X b n) F'; have hh':=creekS_w _ (hp i) hU h (vaneW X b n)
     have hC: Fest (2 * K n) E (M i.appr) (W i.upT) T':= HM _ _ _ a hU hZ (ho i.upT) (ch_fest (ih he hN hx) (ho i.upT) hv)
     intro T e hz j
     by_cases hP : 1<T.card
     · rw [if_pos hP, show rift (V n) (F n)=rift (V n) T' from ?_]; swap
       · have hp : F n=creekT (heights X ν D' i.appr) a (vaneW X b i.i) (F i.upT.i):= by unfold F ownerU; rw [ledgerR, if_pos hN]; rfl
         rw [hp]; exact rift_pass (r_rules ht X.S) (rule_w ..)
       apply owns_mono (sun_step hh' (rule_w X.S ρ (p s).K n) (vast_r ht ρ X.S) (hw.irrigate _) (hC e hz j T) hP) le_rfl
       have hq (p:Finset I):0 ≤ ∏ k∈p,A k s:= prod_nonneg fun i hi=> hA _ _
       let H':=Real.exp (-K n*(ρ*swell X.S i.K n)); have hH:0≤H':= (Real.exp_pos _).le
       apply le_trans (b:=Real.exp (-χ)*∏ k∈T,A k s)
       · calc
           _= M i.appr*H i.upT^T.card * H' *(∏ k∈T,A k s):= by unfold W boon; dsimp only [High.upT,i]; unfold H' K; ring -- i.K defeq
           _≤ C i * H' * (∏ k∈T,A k s):= mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (hL _) (card_le_univ T)) (hM.positive _)) hH) (hq _)
           _≤_:= mul_le_mul_of_nonneg_right (Hq i ρ χ hv hx) (hq _)
       exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (hq T) (one_le_pow₀ (hL _))) (Real.exp_pos _|>.le)
     rw [if_neg hP,one_mul]; apply rift_fe (F:=F n) hu.1 (rule_w ..)
     by_cases h:T.card=1
     · obtain ⟨k,rfl⟩:= card_eq_one.mp h
       let U'(k:I):=U s k n; simp_rw [show ∀ x,F n x {k}=markZ U' x {k} from fun _=>hu.2 ..]
       exact H' _ hz j k i.lowT
     have hx:=ho i.lowT; rw [show T=∅ from card_eq_zero.mp (by omega)]; simp_rw [show ∀ x,F n x ∅=0 from hu.1.void]; exact owns_none _ _ (hx.pos _) _ _ _
end account
end YM.RG08.Creek
