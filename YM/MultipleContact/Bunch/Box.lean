import YM.MergeProof.North.Brim
import YM.MultipleContact.Bunch.Sale
import YM.MultipleContact.Matching.Broad
import YM.MergeProof.North.Siroco
set_option autoImplicit false
noncomputable section
namespace YM.MultipleContact.Bunching
open Matching
variable {α:Type}[Fintype α][Inhabited α][DecidableEq α]
open YM.MergeProof YM.MergeProof.Ribbons
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Source Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil Next.Rank
open Extra.Trajectories MergeProof.Float Station Next.Rank.Spindle Cells
open scoped Topology BigOperators Classical
section
open Relay Exponential Extraction Bid PhysicalNext.Repeat.Legato.Bandage
variable {G:Gauge}(C:Family G)(N p J k j m D :ℕ)(t:α→ℕ) (h:ℝ) {r:ℕ→ℕ} {W:Bid.Worth} {u ψ φ δ:ℕ→ℝ} {μ:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
set_option quotPrecheck false
local notation "H"=> C.path
open Next.UVStress
local notation "P"=> C.path.levels.budget
local notation "Y"=> C.path.levels
local notation "V"=> Site (C.side J p)
local notation "rad"=> fuga C.path.levels (m+1)
variable (T:∀s:α,C.label (t s)) (hf:J ≤ k) (hk:k ≤ m) (hm:m+1 < j) (F:Extraction.Order)
local notation "loss!"=>(fun (x:α → Cover) (N p:ℕ)=> loss C N p j D t h rad T x)
variable (hh:C.Makes)(hR:Created C)(hp:Scrim C W u ψ φ δ (fly C.path.levels) r μ)
variable {i₀:ℕ}{σ χ:ℕ→ℝ}
variable (lamp:Side)(b a e X η c:ℝ)
local notation "A"=> fun i=> expenditure C j m t h i b
variable (hT:∀ i,(C.labels.level (t i)).coeffSize (T i) ≤ b)
local notation "W'"=> basket C.path.levels (lamp*C.S.block m) j (m+1) δ φ η A
local notation "P'"=> (C.path.levels.budget (m+1))
local notation "B!"=> ((P').B^2+1+2*Matching.patch C.path.levels (lamp*C.S.block m) (m+1))
structure Box (bgt ε:ℝ) : Prop where
    corners : ∀ x:α → Cover, x default=0 → (∀s t':α,s≠t' → rad/16≤ ‖C.S.gridPoint j (x s- x t')‖)→ (∀s,‖C.S.gridPoint j (x s)‖≤4*topZone C.path.levels (lamp*C.S.block m) (m+1)) → ∃ z:ℕ×ℕ→ C.label D,  F.late fun N p=> ∃ hJ: J≤N, ‖z (N,p)‖≤ bgt ∧ Interior ((center C.S p hJ 0).chamber 0) ((loss!) x N p (z (N,p)))∧ (center C.S p hJ 0).rootTest (C.beta N p) ((loss!) x N p (z (N,p))) ≤ ε
local notation "L'"=> C.S.a J
-- L.lower arbitrary.X
include hh hp hR hT hm hf hk
lemma bunch_box (hb:0<b)(hw:0<c)(r₀:Stock.Tabs C.path.levels)(hx:Stock.Tabs.opens C.path.levels 1 J k)(hK:C.ref D ≤ k)(hT':∀i,C.ref (t i) ≤ j)(hW:32*topZone C.path.levels (lamp*C.S.block m) (m+1) ≤ L')
   (Y' H':ℕ→ℝ)(hr:Wares C (δ:=δ) (r:=r) (μ:=μ) i₀ D χ δ H')(hg:BatchRibbons.Thor (slot:=α) C.path δ r μ σ χ i₀)(hα:division C (α:=α) (r:=r) (δ:=χ) i₀ Y')(hI:i₀ ≤ m)(HE:X=H' m)(HB:η=Y' (m+1)) (hR':GridApprox.room C.path.levels J m (lensScope C D))
   (hΩ:C.S.a (m+1) * B! ≤ C.S.a J)(hL:march (fun _:Unit=>c) φ k m () ≤ δ m * (W'/(16*X)))
   (hV:0 < W')(hA:4*(1+(C.path.levels.params m).columns)*(2*(C.S.a (m+1)^D*(X*(4*(1/W')))))≤ e)
   (hC:32*(1+(C.path.levels.params m).columns)*c * ‖alto C.path k D‖*(e/gainChart C.path m k) ≤ fly C.path.levels D k/2) :
   Box C J -- edit params auto order check
     j m D t h T F lamp ((lista C D m)*(2*e)) (2*(stakes C J k/c)):= by
   constructor; intro x hx0 hq hhq
   have hY:= hf.trans (hk.trans m.le_succ)
   let Q:= lista C D m
   have hP: 0≤ Q := by dsimp [Q,lista]; exact Finset.prod_nonneg fun i _=>mul_nonneg (zero_le_one.trans (C.path.levels.params (i+1)).columns_ge) (by positivity)
   have hQ := quota_again _ _ _ hh (hK.trans hk)
   let Qtt:= Q*(2*e); let A':=2*(stakes C J k /c)
   have hw'':∀ᶠ i:ℕ×ℕ in F.fuse,∃ (ht:J ≤ i.fst) (v:C.label D),‖v‖≤ Qtt∧ Interior ((center C.S i.2 ht 0).chamber 0) ((loss!) x i.1 i.2 v)∧ (center C.S i.2 ht 0).rootTest (C.beta i.1 i.2) ((loss!) x i.1 i.2 v)≤A':=by
      --have hp₀:∀ᶠ p':ℕ in F.per.cofinal.toFilter, True:=Eventually.of_forall fun _=>trivial -- delete
      have hp':∀ᶠ p':ℕ in (atTop:Filter ℕ), (∀ s:α,C.S.place (wrap (C.side j p') (x s))=C.S.gridPoint j (x s)) ∧ ∀s t':α,C.S.place (wrap (C.side j p') (x s) - wrap (C.side j p') (x t')) = C.S.gridPoint j (x s- x t') :=by
         refine (Filter.eventually_all.mpr fun s=>faraway C j (x s)).and (Filter.eventually_all.mpr fun s=> Filter.eventually_all.mpr fun t'=>?_)
         filter_upwards [faraway C j (x s-x t')] with p hp; rwa [← map_sub]
      rw [Extraction.Order.fused,Extraction.Order.late]; filter_upwards [F.per.cofinal.eventually hp'] with p hp'
      filter_upwards [F.mesh.cofinal.eventually (eventually_gt_atTop j),Filter.eventually_all.mpr (fun s=>F.mesh.cofinal.eventually (near_center C J (t s) hh)), F.mesh.cofinal.eventually (near_center C J D hh)] with N hj ht hS
      let n:=F.mesh N; let q:=F.per p; have hh':J≤n:= by change j<n at hj; omega
      change ∃ (hx:J ≤ n) (v:C.label D), _; refine ⟨hh',?_⟩
      let ℓ:= wrap (C.side j q) ∘ x; let Z:= center C.S q hh' 0
      have hq' : 8* ‖C.S.place (0:Site (C.side n q))‖ ≤ C.S.a J:=by rw [latzero]; simp [(C.S.a_pos J).le]
      have hl(s:α) : Interior (Z.chamber 0) (C.O n q (T s) ((Cells.location C.S j n q ∘ x) s)):=by
          apply ht s hh'; have hN:j ≤ n:= (show j < n from hj).le; dsimp only [Function.comp_apply]; rw [Cells.location,dif_pos hN, C.S.embeds_place (C.S.toDepth hN q),hp'.1 s]; linarith only [hhq s,hW]
      have hΩ' : (((Y|>.budget (m+1)).B)^2+1+2*Matching.patch C.path.levels (lamp*C.S.block m) (m+1)) ≤ (C.S.toDepth hY q).count.val:=by
          exact_mod_cast (le_of_mul_le_mul_left (hΩ.trans_eq (C.S.embeds_scale (C.S.toDepth hY q)).symm) (C.S.a_pos _))
      obtain ⟨v,hq,Hx,hy⟩:= vendor' C n q J k j m D t h x T hf hk hm hj hh hR hp lamp b e X η c hT hb hw r₀ hx hK hT' hx0
          (fun s z hs=>show _ ≤ ‖C.S.place _‖ from by dsimp [Function.comp_apply]; rw [hp'.2 s z]; exact hq s z hs)
          (fun s=>show ‖C.S.place _‖≤4*topZone C.path.levels (lamp*C.S.block m) (m+1) from by dsimp [Function.comp_apply]; rw [hp'.1 s]; exact hhq s) hl (fun v=>hS hh' q _ hq' v) Y' H' hr hg hα hI HE HB hR' hΩ' hL hV hA hC
      refine ⟨v,(hQ n q v ?_).trans (mul_le_mul_of_nonneg_left hq hP),Hx,hy⟩; change j < n at hj;omega
   let pred (i:ℕ×ℕ)(v:C.label D):Prop:=∃ hV:J ≤ i.1, ‖v‖≤ Qtt ∧ Interior ((center C.S i.2 hV 0).chamber 0) ((loss!) x i.1 i.2 v) ∧ (center C.S i.2 hV 0).rootTest (C.beta i.1 i.2) ((loss!) x i.1 i.2 v) ≤ A'
   have he : ∀ᶠ i:ℕ×ℕ in F.fuse, ∃ v,pred i v:=hw''.mono fun i h=> by obtain ⟨hi,v,h,r⟩:=h; exact ⟨v,hi,h,r⟩
   let z(i:ℕ×ℕ): C.label D:=if h:∃ v,pred i v then h.choose else 0
   refine ⟨z,?_⟩; change ∀ᶠ i:ℕ×ℕ in F.fuse, pred i (z i); exact he.mono fun i h=>by unfold z;rw [dif_pos h];exact h.choose_spec
end
end YM.MultipleContact.Bunching
