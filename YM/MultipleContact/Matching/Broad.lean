import YM.MergeProof.North.Brim
import YM.MultipleContact.Matching.Costs
import YM.MergeProof.North.Siroco
set_option autoImplicit false
noncomputable section
namespace YM.MultipleContact.Matching
open YM.MergeProof YM.MergeProof.Ribbons
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Source Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil Next.Rank
open Extra.Trajectories MergeProof.Float Station Next.Rank.Spindle Cells
open scoped Topology BigOperators Classical
section
open Relay Exponential Extraction Bid PhysicalNext.Repeat.Legato.Bandage
variable {G:Gauge}(C:Family G)(N p J k j m D d t:ℕ) (h:ℝ) {r:ℕ→ℕ} {W:Bid.Worth} {u ψ φ δ:ℕ→ℝ} {μ:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
set_option quotPrecheck false
local notation "H"=> C.path
open Next.UVStress
def lista (C:Family G)(D m:ℕ) :ℝ:=∏ k∈range (m+1), (C.path.levels.params (k+1)).columns * ((C.S.block k).val : ℝ)^D
def Price (C:Family G)(m:ℕ):ℝ:= ∏ i∈range (m+1),(C.path.levels.params (i+1)).columns
lemma quota_again (hq:C.Makes)(hK:C.ref D ≤ m):∀ N p (x:C.book.Ref D),m ≤ N → ‖x‖≤ lista C D m*quota C D m N p x:=by
    let c i:= (C.path.levels.params (i+1)).columns * ((C.path.S.block i).val : ℝ)^D
    have hh : ∀ i:ℕ,1≤ c i:= fun i=>one_le_mul_of_one_le_of_one_le (C.path.levels.params (i+1)).columns_ge (one_le_pow₀ (show 1 ≤ ((C.S.block i).val:ℝ) from by exact_mod_cast (C.S.block i).pos))
    suffices hy:∀ k:ℕ,k ≤ m→C.ref D≤k→∀ N p (x:C.book.Ref D),m ≤ N→ ‖x‖≤ (∏ j∈range k,c j)*quota C D k N p x from fun _ _ x hm=>(hy m le_rfl hK _ _ x hm).trans (mul_le_mul_of_nonneg_right (by
        unfold lista; change (∏ j∈range m,_ ) ≤ ∏ j∈range (m+1), _ ; rw [Finset.prod_range_succ]; exact le_mul_of_one_le_right (Finset.prod_nonneg fun i _=>zero_le_one.trans (hh i)) (hh m)) (by rw [quota,Labels.Frame.coeffSize]; exact Finset.sum_nonneg fun _ _=> norm_nonneg _))
    intro k hk hv; induction k,hv using Nat.le_induction with
    | base=> intro N p x hm; refine le_trans ?_ (le_mul_of_one_le_left (by rw [quota]; change 0≤∑ _,_; positivity) (one_le_prod (fun j _=>hh j))); rw [quota,C.normalized hq (hk.trans hm)]; exact (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)).mpr (fun i=>Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ i))
    | succ k hk' ih=> intro N p x hm
                      have ht:k ≤ m:=by omega
                      have hh':k+1 ≤ N:=hk.trans hm; -- actually m≤N, k+1≤N
                      refine (ih ht N p _ hm).trans ?_
                      rw [Finset.prod_range_succ,mul_assoc]
                      exact mul_le_mul_of_nonneg_left ((hq.calibrated D N p (hk'.trans (ht.trans hm))).front k hk' hh' _) (Finset.prod_nonneg (fun i _=> zero_le_one.trans (hh i)))
local notation "P"=> C.path.levels.budget
local notation "Y"=> C.path.levels
local notation "V"=> Site (C.side J p)
local notation "rad"=> fuga C.path.levels (m+1)
variable(B: C.label d) (T:C.label t) (hf:J ≤ k) (hk:k ≤ m) (hm:m+1 < j) (F:Extraction.Order)
local notation "f"=> (fun (x:Cover) (N p:ℕ)=> residue (C:=C) (D:=D) h rad T B j x N p)
variable (hh:C.Makes)(hR:Created C)(hp:Scrim C W u ψ φ δ (fly C.path.levels) r μ)
variable {i₀:ℕ}{σ χ:ℕ→ℝ}
variable (b a e X η c:ℝ)
local notation "A"=> sums C j m d t h b a
variable (hB:(C.labels.level d).coeffSize B ≤ a) (hT:(C.labels.level t).coeffSize T ≤ b)
local notation "W'"=> wend C.path.levels (C.S.block m) j (m+1) δ φ η A
local notation "P'"=> (C.path.levels.budget (m+1))
local notation "B!"=> ((P').B^2+1+2*patch C.path.levels (C.S.block m) (m+1))
structure Box (bgt ε:ℝ) : Prop where
    corners : ∀ x:Cover, rad/16≤ ‖C.S.gridPoint j x‖→ ‖C.S.gridPoint j x‖≤4*topZone C.path.levels (C.S.block m) (m+1) → ∃ z:ℕ×ℕ→ C.label D,  F.late fun N p=> ∃ hJ: J≤N, ‖z (N,p)‖≤ bgt ∧ Interior ((center C.S p hJ 0).chamber 0) (f x N p (z (N,p)))∧ (center C.S p hJ 0).rootTest (C.beta N p) (f x N p (z (N,p))) ≤ ε
local notation "L'"=> C.S.a J
-- L.lower arbitrary.X
include hh hp hR hB hT hm hf hk
lemma corner (ha:0<a)(hb:0<b)(hw:0<c)(r₀:Stock.Tabs C.path.levels)(hx:Stock.Tabs.opens C.path.levels 1 J k)(hK:C.ref D ≤ k)(h':C.ref d ≤ j)(hT':C.ref t ≤ j)(hW:32*topZone C.path.levels (C.S.block m) (m+1) ≤ L')
   (Y' H':ℕ→ℝ)(hr:Wares C (δ:=δ) (r:=r) (μ:=μ) i₀ D χ Y' H')(hI:i₀ ≤ m)(HE:X=H' m)(HB:η=Y' (m+1)) (hR':GridApprox.room C.path.levels J m (lensScope C D))
   (hΩ:C.S.a (m+1) * B! ≤ C.S.a J)(hL:march (fun _:Unit=>c) φ k m () ≤ δ m * (W'/(16*X)))
   (hV:0 < W')(hA:4*(1+(C.path.levels.params m).columns)*(2*(C.S.a (m+1)^D*(X*(4*(1/W')))))≤ e)
   (hC:32*(1+(C.path.levels.params m).columns)*c * ‖alto C.path k D‖*(e/gainChart C.path m k) ≤ fly C.path.levels D k/2) :
   Box C J -- edit params auto order check
     j m D d t h B T F ((lista C D m)*(2*e)) (2*(stakes C J k/c)):= by
   constructor; intro x hq hhq
   have hY:= hf.trans (hk.trans m.le_succ)
   let Q:= lista C D m
   have hP: 0≤ Q := by dsimp [Q,lista]; exact Finset.prod_nonneg fun i _=>mul_nonneg (zero_le_one.trans (C.path.levels.params (i+1)).columns_ge) (by positivity)
   have hQ := quota_again _ _ _ hh (hK.trans hk)
   let Qtt:= Q*(2*e); let A':=2*(stakes C J k /c)
   have hw':∀ᶠ i:ℕ×ℕ in F.fuse,∃ (ht:J ≤ i.fst) (v:C.label D),‖v‖≤ Qtt∧ Interior ((center C.S i.2 ht 0).chamber 0) (f x i.1 i.2 v)∧ (center C.S i.2 ht 0).rootTest (C.beta i.1 i.2) (f x i.1 i.2 v)≤A':=by
       rw [Extraction.Order.fused,Extraction.Order.late]; filter_upwards [F.per.cofinal.eventually (faraway C j x)] with p hp'
       filter_upwards [F.mesh.cofinal.eventually (eventually_gt_atTop j),F.mesh.cofinal.eventually (near_center C J d hh), F.mesh.cofinal.eventually (near_center C J D hh), F.mesh.cofinal.eventually (near_center C J t hh)] with N hj hs hS ht
       let n:=F.mesh N; let q:=F.per p; have hh':J≤n:= by change j<n at hj; omega
       change ∃ (hx:J ≤ n) (v:C.label D), _; refine ⟨hh',?_⟩
       let ℓ:= wrap (C.side j q) x; have hp0 : C.S.place ℓ= C.S.gridPoint j x:=hp'; let Z:= center C.S q hh' 0
       have hq' : 8* ‖C.S.place (0:Site (C.side n q))‖ ≤ C.S.a J:=by rw [latzero]; simp [(C.S.a_pos J).le]
       have hl : Interior (Z.chamber 0) (C.O n q T (Cells.location C.S j n q x)):=by
          apply ht hh'; have hN:j ≤ n:= (show j < n from hj).le; rw [Cells.location,dif_pos hN, C.S.embeds_place (C.S.toDepth hN q),hp']; linarith only [hhq,hW]
       have hΩ' : (((Y|>.budget (m+1)).B)^2+1+2*patch C.path.levels (C.S.block m) (m+1)) ≤ (C.S.toDepth hY q).count.val:=by
          exact_mod_cast (le_of_mul_le_mul_left (hΩ.trans_eq (C.S.embeds_scale (C.S.toDepth hY q)).symm) (C.S.a_pos _))
       obtain ⟨v,hq,H',hx⟩:= vendor C n q J k j m D d t h x B T hf hk hm hj hh hR hp b a e X η c hB hT ha hb hw r₀ hx hK h' hT' (show _ ≤ ‖C.S.place ℓ‖ from hp0.symm ▸ hq) (show ‖C.S.place ℓ‖≤4*topZone C.path.levels (C.S.block m) (m+1) from hp0.symm ▸ hhq) hl (hs hh' q _ hq' B) (fun v=>hS hh' q _ hq' v) Y' H' hr hI HE HB hR' hΩ' hL hV hA hC
       refine ⟨v,(hQ n q v ?_).trans (mul_le_mul_of_nonneg_left hq hP),H',hx⟩; change j < n at hj;omega
   let pred (i:ℕ×ℕ)(v:C.label D):Prop:=∃ hV:J ≤ i.1, ‖v‖≤ Qtt ∧ Interior ((center C.S i.2 hV 0).chamber 0) (f x i.1 i.2 v) ∧ (center C.S i.2 hV 0).rootTest (C.beta i.1 i.2) (f x i.1 i.2 v) ≤ A'
   have he : ∀ᶠ i:ℕ×ℕ in F.fuse, ∃ v,pred i v:=hw'.mono fun i h=> by obtain ⟨hi,v,h,r⟩:=h; exact ⟨v,hi,h,r⟩
   let z(i:ℕ×ℕ): C.label D:=if h:∃ v,pred i v then h.choose else 0
   refine ⟨z,?_⟩; change ∀ᶠ i:ℕ×ℕ in F.fuse, pred i (z i); exact he.mono fun i h=>by unfold z;rw [dif_pos h];exact h.choose_spec
end
end YM.MultipleContact.Matching
