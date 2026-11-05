import YM.UVExtension.Beach.Tracks
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Beach
open Function Filter Set Metric Lattice RG Wilson
open MergeProof.Ribbons.Note
open Extraction Fallow Poppy Tide Swell Lamppost Spire Pier Rafter
open scoped Topology BigOperators Classical ContDiff
variable {n j N m:ℕ} (S:Schedule)
local notation "X"=> Tabletop n
local notation "D"=> Points n
variable {A:Set (Points n)}(h:IsOpen A){a b:ℝ}(ha:0<a)
   (F:ℕ→Row a→ Tabletop n→ℂ) (p:ℕ)
set_option quotPrecheck false
local notation "T"=> desk a ha
local notation "V"=> Row a
variable (L:List (Axel n))
structure Plateau (S:Schedule)(A:Set (Points n))(F:ℕ→Row a→ Tabletop n→ℂ)(m:ℕ):Prop where
   fits(L:List (Axel n))(h:L.length ≤ m)(K:Set (Points n))(hk:IsCompact K)(hK:K⊆A):∃ b:ℝ,0 ≤ b ∧ ∀ᶠ N in atTop,∀ v x,tag (S.a N) x∈ K →‖rake (S.a N) (F N v) L x‖≤ b
variable (Q:Patio S a b ha F p A) (E:Plateau S A F (m+1)) (hl:L.length ≤ m)
-- Uniform real errors of layout approximation to horizontal densities.
include E hl h
lemma bay (K:Set (Points n))(hK:K⊆ A)(hk:IsCompact K): ∀ᶠ j in atTop,∀ N (hx:j ≤ N)(x:X),Extraction.tag (S.a N) x∈ K → ∀ v:Row a, ‖round S F L N p j hx x v-rake (S.a N) (F N v) L x‖ ≤ expS S (-(1/2)) j:= by
   obtain ⟨r,hr,hR⟩:= hk.exists_cthickening_subset_open h hK; let Y:=cthickening r K
   choose V₀ hV hB using fun d:Axel n=> E.fits (d::L) (by simpa) Y hk.cthickening hR; let Q:= ∑ i,V₀ i; have he:0 ≤ Q:= Finset.sum_nonneg fun i _=> hV i
   have hh : ∀ᶠ i in atTop,∀ v:Row a,capping (S.a i) Q (rake (S.a i) (F i v) L) Y:= (eventually_all.mpr hB).mono fun i hi z b p hx=> (hi b z p hx).trans (Finset.single_le_sum (fun i _=> hV i) (Finset.mem_univ _))
   obtain ⟨i,hi⟩:= eventually_atTop.mp hh
   let c:ℝ:= L.length+(4:ℝ)*n; let v':= ((n:ℝ)*4*Q); have hc:0 ≤ c:=by unfold c; positivity
   have hz:0≤v':=mul_nonneg (by positivity) he
   let d:=1+v'*c; have hd:0<d:=by unfold d; positivity
   have hP:= ((notes S d hd).mills (note_a S)).outweigh (bell_exp S (-(1/2))) (by norm_num)
   have hC:Tendsto (fun i=>c*S.a i) atTop (𝓝 0):=by simpa only [mul_zero] using S.shrinks.const_mul c
   filter_upwards [eventually_ge_atTop i,hP, hC.eventually (ge_mem_nhds (half_pos hr))] with j hj hP hr' N hN x hx v
   let q:= Extraction.address (S.a j) (tag (S.a N) x); let Z:= scoop S p hN q
   unfold round zoom; rw [canoe S (F N v) p hN]; refine tiered _ _ (S.toDepth hN p).count.property (S.a_pos _) _ (S.embeds_scale _) _ _ _ _ (fun y hy=>?_)
   have h₁ : dist (tag (S.a N) Z) (tag (S.a N) x) ≤ (4*n:ℝ)*S.a j:= by unfold Z; rw [← scoop_tag]; exact approximate (S.a_pos _) _
   have ht : dist (tag (S.a N) y) (tag (S.a N) x) ≤ c*S.a j:=le_trans (dist_triangle _ (tag (S.a N) Z) _) ((add_le_add hy h₁).trans_eq (by unfold c; ring))
   rw [← dist_eq_norm]; refine (Poppy.hop (S.a_pos _) (hi N (hj.trans hN) v) he _ _ hx (r:=r/2) (cthickening_mono (by linarith) K) (ht.trans hr')).trans ((mul_le_mul_of_nonneg_left ht hz).trans (le_trans ?_ hP))
   rw [←mul_assoc]; exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (S.a_pos _).le
omit E hl h
private lemma trueR (N:ℕ)(x:X): round S F L N p N le_rfl x= fun v=> rake (S.a N) (F N v) L x:=by
    unfold round zoom; rw [Extraction.address_matched (S.a_pos _)]; have hx : scoop S (n:=n) p (le_refl N)= id:=by
       funext x; change (S.toDepth _ p).count.val • _= _; rw [show (S.toDepth (le_refl N) p).count.val=1 from ?_,one_smul]; rfl
       unfold Schedule.toDepth; simp only [Nat.sub_self]; rfl
    rw [hx]; rfl
include ha h Q E
lemma whale (hq:S.Gentle): ∃ s:ℝ, ∃ hs:0<s, ∃ hv:s ≤ a, ∀ (L:List (Axel n)), L.length≤ m →∀ K:Set (Points n),K⊆ A→IsCompact K→ ∃ M:ℝ,0≤ M∧∀ᶠ N in atTop,∀ x:X, tag (S.a N) x∈K→ Sail (desk s hs) (fun d:Row s=> rake (S.a N) (F N ⟨d.val,d.2.trans_le hv⟩) L x) M:=by
   obtain ⟨z,hz,hM⟩:= charge S ha F p Q m; obtain ⟨s,hs,hp,p',hP⟩:= cordage S hq z hz ha (1/2) (by norm_num); refine ⟨s,hs,hp,fun L hL K hK hk=>?_⟩
   obtain ⟨i,hi⟩:= eventually_atTop.mp ((hP.and (bay S h F p L E hL K hK hk)).and (rocky S h ha F p L Q K hk hK hL 0 _ hz hM)) -- hp involves m. goals
   let M:= max 0 (expS S z i+p'); refine ⟨M,le_max_left ..,?_⟩
   filter_upwards [eventually_ge_atTop i] with N hN x hx
   let Z(j:ℕ):V→ℂ:= if h:j≤N then round S F L N p j h x else fun _=>0
   have hv j (h:j≤N): Z j= round S F L N p j h x:= dif_pos h; have hV: Z N=fun d:Row a=> rake (S.a N) (F N d) L x:= (hv _ le_rfl).trans (trueR ..)
   have hG:= (hi i le_rfl).1.1 N hN Z (fun j hj h=>hv j h|>.symm ▸ (hi j hj).2 N h x hx) (fun j hj h d=> (?_)); swap; · rw [hV,hv j h]; exact (hi j hj).1.2 N h x hx d
   rw [hV] at hG; exact hG.mono (le_max_right ..)
end YM.UVExtension.Beach
