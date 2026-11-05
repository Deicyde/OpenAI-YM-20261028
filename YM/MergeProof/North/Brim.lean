import YM.MergeProof.North.Cent
import YM.MergeProof.North.Siroco
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Source Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil Next.Rank
open Extra.Trajectories MergeProof.Float Station Next.Rank.Spindle Cells
open scoped Topology BigOperators Classical
section
open Relay Exponential Extraction Bid PhysicalNext.Repeat.Legato.Bandage
variable {G:Gauge}(C:Family G)(N p J k j m D d h:ℕ) {r:ℕ→ℕ} {W:Bid.Worth} {u ψ φ δ:ℕ→ℝ} {μ:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
set_option quotPrecheck false
local notation "H"=> C.path
local notation "P"=> C.path.levels.budget
local notation "Y"=> C.path.levels
local notation "V"=> Site (C.side J p)
local notation "rad"=> fuga C.path.levels (m+1)
variable (x:Cover)(B: C.label d) (T:C.label 4) (hf:J ≤ k) (hk:k ≤ m) (hm:m+1 < j) (F:Extraction.Order)
local notation "f"=> (fun (x:Cover) (N p:ℕ)=> Next.UVStress.fragment (C:=C) (D:=D) (d:=d) h rad T B j x N p)
variable (hh:C.Makes)(hR:Created C)(hp:Scrim C W u ψ φ δ (fly C.path.levels) r μ)
variable {i₀:ℕ}{σ χ:ℕ→ℝ}
variable (b a e X η c:ℝ)
local notation "A"=> whims C j m d h b a
variable (hB:(C.labels.level d).coeffSize B ≤ a) (hT:(C.labels.level 4).coeffSize T ≤ b)
local notation "W'"=> ventola C.path.levels j (m+1) δ φ η A
local notation "P'"=> (C.path.levels.budget (m+1))
local notation "B!"=> ((P').B^2+1+2*polls C.path.levels (m+1))
lemma faraway : ∀ᶠ p':ℕ in atTop, C.S.place (wrap (C.side j p') x) = C.S.gridPoint j x:=by
   have ht : ∀ i:Axis,∀ᶠ p in atTop,-((C.side j p).val:ℤ)<2*x i ∧ 2*x i ≤(C.side j p).val:=by
      intro i; filter_upwards [C.S.period_strict.tendsto_atTop.eventually_ge_atTop (4*(x i).natAbs+1)] with p hp; have hh : (C.S.period p).val≤ (C.side j p).val:= Nat.le_mul_of_pos_right _ (C.S.denominator j).pos; omega
   filter_upwards [eventually_all.mpr ht] with i he; unfold Schedule.place; rw [show lift (wrap _ x)=x from lift_eq_iff.mpr ⟨rfl,he⟩]
structure ShellNode (ε:ℝ) : Prop where
    corners : ∀ x:Cover, rad/16≤ ‖C.S.gridPoint j x‖→ ‖C.S.gridPoint j x‖≤4*rad → ∃ z:ℕ×ℕ→ C.label D,∃ A' :ℝ, F.late fun N p=> ∃ hJ: J≤N, ‖z (N,p)‖≤ A' ∧ Interior ((center C.S p hJ 0).chamber 0) (f x N p (z (N,p)))∧ (center C.S p hJ 0).rootTest (C.beta N p) (f x N p (z (N,p))) ≤ ε
local notation "L'"=> C.S.a J
-- L.lower arbitrary.X
include hh hp hR hB hT hm hf hk
lemma bricks (ha:0<a)(hb:0<b)(hw:0<c)(r₀:Stock.Tabs C.path.levels)(hx:Stock.Tabs.opens C.path.levels 1 J k)(hK:C.ref D ≤ k)(h':C.ref d ≤ j)(hT':C.ref 4 ≤ j)(hW:32*rad ≤ L')
   (Y' H':ℕ→ℝ)(hr:Wares C (δ:=δ) (r:=r) (μ:=μ) i₀ D χ Y' H')(hI:i₀ ≤ m)(HE:X=H' m)(HB:η=Y' (m+1)) (hR':GridApprox.room C.path.levels J m (lensScope C D))
   (hΩ:C.S.a (m+1) * B! ≤ C.S.a J)(hL:march (fun _:Unit=>c) φ k m () ≤ δ m * (W'/(16*X)))
   (hV:0 < W')(hA:4*(1+(C.path.levels.params m).columns)*(2*(C.S.a (m+1)^D*(X*(4*(1/W')))))≤ e)
   (hC:32*(1+(C.path.levels.params m).columns)*c * ‖alto C.path k D‖*(e/gainChart C.path m k) ≤ fly C.path.levels D k/2) :
   ShellNode C J -- edit params auto order check
     j m D d h B T F (2*(stakes C J k/c)):= by
   constructor; intro x hq hhq
   have hY:= hf.trans (hk.trans m.le_succ)
   obtain ⟨Q,hP,hQ⟩:= Next.UVStress.quota_stop C hh (hK.trans hk)
   let Qtt:= Q*(2*e); let A':=2*(stakes C J k /c)
   have hw':∀ᶠ i:ℕ×ℕ in F.fuse,∃ (ht:J ≤ i.fst) (v:C.label D),‖v‖≤ Qtt∧ Interior ((center C.S i.2 ht 0).chamber 0) (f x i.1 i.2 v)∧ (center C.S i.2 ht 0).rootTest (C.beta i.1 i.2) (f x i.1 i.2 v)≤A':=by
       rw [Extraction.Order.fused,Extraction.Order.late]; filter_upwards [F.per.cofinal.eventually (faraway C j x)] with p hp'
       filter_upwards [F.mesh.cofinal.eventually (eventually_gt_atTop j),F.mesh.cofinal.eventually (near_center C J d hh), F.mesh.cofinal.eventually (near_center C J D hh), F.mesh.cofinal.eventually (near_center C J 4 hh)] with N hj hs hS ht
       let n:=F.mesh N; let q:=F.per p; have hh':J≤n:= by change j<n at hj; omega
       change ∃ (hx:J ≤ n) (v:C.label D), _; refine ⟨hh',?_⟩
       let ℓ:= wrap (C.side j q) x; have hp0 : C.S.place ℓ= C.S.gridPoint j x:=hp'; let Z:= center C.S q hh' 0
       have hq' : 8* ‖C.S.place (0:Site (C.side n q))‖ ≤ C.S.a J:=by rw [latzero]; simp [(C.S.a_pos J).le]
       have hl : Interior (Z.chamber 0) (C.O n q T (Cells.location C.S j n q x)):=by
          apply ht hh'; have hN:j ≤ n:= (show j < n from hj).le; rw [Cells.location,dif_pos hN, C.S.embeds_place (C.S.toDepth hN q),hp']; linarith only [hhq,hW]
       have hΩ' : (((Y|>.budget (m+1)).B)^2+1+2*polls C.path.levels (m+1)) ≤ (C.S.toDepth hY q).count.val:=by
          exact_mod_cast (le_of_mul_le_mul_left (hΩ.trans_eq (C.S.embeds_scale (C.S.toDepth hY q)).symm) (C.S.a_pos _))
       obtain ⟨v,hq,H',hx⟩:= sales C n q J k j m D d h x B T hf hk hm hj hh hR hp b a e X η c hB hT ha hb hw r₀ hx hK h' hT' (show _ ≤ ‖C.S.place ℓ‖ from hp0.symm ▸ hq) (show ‖C.S.place ℓ‖≤4*rad from hp0.symm ▸ hhq) hl (hs hh' q _ hq' B) (fun v=>hS hh' q _ hq' v) Y' H' hr hI HE HB hR' hΩ' hL hV hA hC
       refine ⟨v,(hQ n q v ?_).trans (mul_le_mul_of_nonneg_left hq hP),H',hx⟩; change j < n at hj;omega
   let pred (i:ℕ×ℕ)(v:C.label D):Prop:=∃ hV:J ≤ i.1, ‖v‖≤ Qtt ∧ Interior ((center C.S i.2 hV 0).chamber 0) (f x i.1 i.2 v) ∧ (center C.S i.2 hV 0).rootTest (C.beta i.1 i.2) (f x i.1 i.2 v) ≤ A'
   have he : ∀ᶠ i:ℕ×ℕ in F.fuse, ∃ v,pred i v:=hw'.mono fun i h=> by obtain ⟨hi,v,h,r⟩:=h; exact ⟨v,hi,h,r⟩
   let z(i:ℕ×ℕ): C.label D:=if h:∃ v,pred i v then h.choose else 0
   refine ⟨z,Qtt,?_⟩; change ∀ᶠ i:ℕ×ℕ in F.fuse, pred i (z i); exact he.mono fun i h=>by unfold z;rw [dif_pos h];exact h.choose_spec
end
end YM.MergeProof.Ribbons
