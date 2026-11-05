import YM.MergeProof.Coast
import YM.Next.RANK.HomeSync

set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Accent
open Finset Function Filter MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Next.Rank Edition Baler Value Glyph Thirst Alarm Push GridApprox.Nil Motion
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge}{n:Side}{V:Type}[Fintype V][DecidableEq V] (o: V→Site n)
variable {u v t e:ℝ} {ι κ:Type} [Fintype ι] [Fintype κ]
variable {Q:Rep G n}
local notation "A"=> Q.activities
variable {d:ℕ} {F:Labels.Frame G d}(T:SectionData F)(D:V→ Coefficient F n)
   {η:Hol G} (h:∀ i,(D i).Format 0 η Q)(s:V→Signed)(x:V→Prop)
   (B:Neat n → Burst G n Q.p.threshold)(β:ℂ)(hb:star β=β)
   (w:V→ℝ)(F0: Support n→ Config G n→veil V)(K:Box n→ Config G n→ veil V)
local notation "P"=> Q.p
set_option quotPrecheck false
local notation "Y"=> elder o B D β h s x
local notation "a"=> (fun i=> radiant β (dye (s i) (x i)) (o i) ((D i).exponentialEntry 0 T Q))
local notation "b"=> (fun i=> sunny Q (D i).forced (dye (s i) (x i)) (o i) β)
lemma gown (hp:IsoVac Q B t) (U:Config G n)(i:Neat n): bar Q.activities (Stock.census V) U i.val=(Alarm.enroll o (B i)).amount U:=by
    change Poly.send _ _=Poly.send _ _; apply congr_arg (Poly.send (quiet V)); change _= ((B i).value U:ℂ); rw [hp.value,Complex.ofReal_tsum,profile,expand_eq]; refine tsum_congr fun j=>?_; have hx: locator (Q.activities.forced j)=i↔ barcode Q.activities j=i.val:= Subtype.ext_iff
    split
    next hv=> rw [if_pos (hx.mpr hv)];rfl
    next hv=> rw [if_neg (hx.not.mpr hv),Complex.ofReal_zero]
include h hb
variable (J:κ→ Lifted G o Q.p.threshold)(h':∀ p:Box n,∀ U:Config G n,K p U=∑ i,(if (attached (J i)).val=p then (J i).amount U else 0))
include h'
omit [Fintype ι] in
lemma scholar (hp:IsoVac Q B t)(U : Config G n) (i:Neat n): gamut B D β h s x J U i=bar Q.activities (Stock.census V) U i.val+Mach (Stock.census V) (fun v=> b v i.val U)+K i.val U:=by
    rw [h',gamut,Fintype.sum_sum_type]; congr 1
    · unfold Elders; rw [Fintype.sum_sum_type]
      have he(i: Neat n): attached (Y (.inl i))=i:= hp.points i
      apply congr_arg₂ (·+·)
      · change (∑ j:Neat n, if attached (Y (Sum.inl j))=i then (Y (Sum.inl j)).amount U else 0)=_
        rw [Finset.sum_eq_single i]
        · rw [if_pos (he i)]; exact (gown o B hp U i).symm -- prop inferred
        · intro j _ hj; rw [he,if_neg hj]
        simp
      rw [Fintype.sum_prod_type]; exact Finset.sum_congr rfl fun m _=> dye_wash o D h s x β hb m i U
    apply Finset.sum_congr rfl; intro j _; dsimp only [Sum.elim_inr]; exact if_congr Subtype.ext_iff rfl rfl -- thunk
lemma glint (hp:IsoVac Q B t) (K':ι →SourceAt G o)(hF:∀ U,∑ i,(K' i).amount Q.p.threshold U=∑ i,F0 i U)
    (ht:∀ i,Flow o i (K i) Q.p.threshold): restore Q a b F0 K = creds B D β h s x J K' T:=by
    funext U; unfold restore creds
    rw [← all_gas,hF,peel];
    · have hm:gamut B D β h s x J U=(fun i:Neat n=>bar Q.activities (Stock.census V) U i.val+Mach (Stock.census V) (fun v=> b v i.val U)+K i.val U):=funext fun i=> scholar o D h s x B β hb K J h' hp U i
      rw [hm]; congr 3; apply congr_arg (· + ∑ i,F0 i U);unfold Mach; exact Finset.sum_congr rfl fun j _=>congr_arg (Poly.send (slot j)) (flags_dot β hb (s j) (x j) _)
    intro i hi; by_contra hz; apply hi; have hh (m:V): b m i U=0:=by
        let z:=dye (s m) (x m); unfold sunny
        let f:= profile Q.activities (D m).forced; obtain ⟨p,rfl⟩:= (puff z (o m)).surjective i
        change β*scalar z (f ((puff z (o m)).symm (puff z (o m) p)) _)=0; rw [Equiv.symm_apply_apply]; unfold f; rw [beacon (Z:= (D m).forced),scalar_z,mul_zero] -- unfold f
        intro h; apply hz; unfold puff; change Sure (sky z (o m) p.1,sky z (o m) p.2); unfold Sure; simp only [shading]; exact ⟨h.1.image _,Finset.image_subset_image h.2⟩
    have h0:= not_not.mp fun h=> hz ((ht i).permits U h|>.2)
    change (bar Q.activities (Stock.census V) U i+_)+_=0; simp_rw [hh]; unfold bar Mach; rw [beacon _ _ i hz,h0]; simp
end YM.MergeProof.Accent
