module DropBox
open Date as Date
open Objeto as Object
open util/ordering[Date] as to

------------------------------------------------------------------------
-- PROJETO ALLOY:  DROPBOX

-- GRUPO: 4

--	João Henrique
--	Luan
--	Caio
-- 	Fabiana 

-- CLIENTE : TIAGO MASSONI

-- PROFESSOR : TIAGO MASSONI

-------------------------------------------------------------------------
-- Usuario 
one sig User {
	storage : set Folder,
	device: set Device -> Date 
}
-- Pasta
sig Folder {
	archives: set Object -> Date
}

-- Arquivos
abstract sig Archive extends Object {
	info : one Info,
   backup : set Backup ->Date,
	permission: set Permission ->Date
}
-- Tipos de arquivos
sig Text extends Archive{}
sig Music extends Archive{}
sig Movie extends Archive{}
sig Image extends Archive{}
sig Rar extends Archive{}
-- Informacao do arquivo
sig Info {}
-- Dispositivos a ser conectado pelo usuario 
abstract sig Device {
	permission : one Permission
}

sig Pc extends Device{}
sig Cell extends Device{}
sig Kindle extends Device{}
sig Tablet extends Device{}

-- Permissao para ler e modificar arquivo

abstract sig Permission{}
one sig Read extends Permission{}
one sig Write_Read extends Permission{}
-- Versões dos arquivos
sig Backup{
}
--------- FATOS
fact Folder{
	-- Toda Pasta deve pertencer a um usuario
   all f : Folder | one f.~storage
}

fact Archive{	
	-- Todo Arquivo deve pertencer a uma pasta
	all d:Archive , t:Date | one d.~(archives.t)
	-- Info deve pertencer apenas a um arquivo
	all i : Info | one i.~info	
	-- Todo arquivo deve ter algum tipo de permissao
	all a:Archive,t:Date  | one a.(permission.t)

	all a:Archive, t:Date | some p:Folder | a in p.(archives.t)
	-- todo Backup esta contido em Arquivo
	all b:Backup, d:Date |some a:Archive | b in (a.(backup.d))
}
fact Versao{}

fact Device{
	-- Todo aparelho que for celular ou kindle sua permissao é Leitura
	all d:Device | (d in Cell || d in Kindle) => (d.permission = Read)
	-- Todo aparelho que for Pc ou Tablet é Leitura e Escrita 
	all d:Device | (d in Pc || d in Tablet) => (d.permission = Write_Read)
}
-- Adiciona Arquivo
-- Remove Arquivo
-- Atualiza Arquivo
fact add_remove_update_archive {
	
	all date: Date-last | 
   let pos = date.next |
   some d:Object, p:Folder | 
   addArchive[d,p,date,pos] ||
	removeArchive[d,p,date,pos]
	-- Modifica backup do arquivo
	 all date: Date-last | let pos = date.next |some a:Archive, b:Backup| updateArchive[a,b,date,pos]

}

-- Adiciona Dispositivos moveis 
--Remove Dispositivos moveus

fact add_remove_update_device {
	all date: Date-last | 
   let pos = date.next |
   some d: Device| 
   addDevice[d,date,pos] ||
	removeDevice[d,date,pos]
}

---- PREDICADOS
pred addArchive[d:Object,p:Folder,t,t':Date] {
 	d !in p.(archives.t)
	(p.archives).t' = (p.archives).t + d
}
pred removeArchive[d:Object,p:Folder,t,t':Date] {
 	d !in p.(archives.t)
	(p.archives).t' = (p.archives).t- d
}

pred updateArchive[a:Archive,b:Backup,d,d':Date] {
	b !in ((a.backup).d)
	(a.backup).d' = b
}
pred addDevice[d:Device, t,t':Date]{
	d !in User.(device.t)
	(User.device).t'= (User.device).t + d
}
pred removeDevice[d:Device, t,t':Date]{
	d !in User.(device.t)
	(User.device).t'= (User.device).t - d
}
------- ASSERTS 

assert todaContaTemPeloMenosPasta{
	   all c:User| some c.storage
}
assert todaPastaDevePertencerUmUsuario{
		all f : Folder | one f.~storage
}
assert todaPastaDeveTerPeloMenosUmArquivo{
	all f: Folder | some f.archives
}
assert todoDispositivoTemUmaPermissao {
	all d:Device | one d.permission
}
assert todoArquivoTemPeloMenosUmBackup {
	all a:Archive | some a.backup

}
assert todoUsuarioTemAlgumArquivo{
	some User.storage.archives
}
assert todoUsuarioTemAlgumDispositivo{
	some User.device
}
assert todoArquivoTemUmaInfo{
	all a:Archive | one a.info
}

-------- CHECKS

check todaContaTemPeloMenosPasta for 10
check todaPastaDevePertencerUmUsuario for 10
check todaPastaDeveTerPeloMenosUmArquivo for 10
check todoDispositivoTemUmaPermissao for 10
check todoArquivoTemPeloMenosUmBackup for 10
check todoUsuarioTemAlgumArquivo for 10
check todoUsuarioTemAlgumDispositivo for 10
check todoArquivoTemUmaInfo for 10

pred show[] {}

run show for 5
