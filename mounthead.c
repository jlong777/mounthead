/********************************************************************************
 * Copyright (C) 2014, University of Alaska Fairbanks
 * International Arctic Research Center
 * Author: James Long, jlong@alaska.edu
 *-------------------------------------------------------------------------------
 * MOUNTHEAD BSD License
 * 
 * Redistribution and use in source and binary forms, with or without 
 * modification, are permitted provided that the following conditions are met:
 * 
 *    * Redistributions of source code must retain the above copyright notice, 
 *      this list of conditions and the following disclaimer.
 *    * Redistributions in binary form must reproduce the above copyright notice,
 *      this list of conditions and the following disclaimer in the documentation
 *      and/or other materials provided with the distribution.
 *    * Neither the name of the University of Alaska Fairbanks nor the names of 
 *      its contributors may be used to endorse or promote products derived from 
 *      this software without specific prior written permission.
 * 
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" 
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE 
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE 
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL 
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR 
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER 
 * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, 
 * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE 
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * ------------------------------------------------------------------------------
 * MOUNTHEAD GPL License
 * 
 * This project consists of free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 * 
 * This resource is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301, USA
 *
 */

/*
 * Build a cluster on-the-fly, using submit-host as head node exporting
 * private mounts.
 *
 * compile: gcc -shared -fPIC -o mounthead.so mounthead.c -Wall
 * and $ sudo mv mounthead.so /lib
 *
 * then place in /etc/slurm-llnl/plugstack.conf (tab delineated)
 *
 * required     /lib/mounthead.so
 *
 * 
 * This work loosely based on a spank script that did private mounts, 
 * author(s) of which escapes me, but I believe it was from LLNL. In
 * doing a search, I see some LLNL C code with the private mount idea at 
 * https://github.com/chaos/slurm-spank-plugins/blob/master/private-mount.c
 */

#define _GNU_SOURCE
#include <arpa/inet.h>
#include <dirent.h>
#include <netdb.h>
#include <pwd.h>
#include <regex.h>
#include <sched.h>
#include <slurm/spank.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <sys/mount.h>
#include <sys/resource.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/time.h>
#include <sys/types.h>
#include <unistd.h>

/* must define this macro for the SLURM plugin loader */
SPANK_PLUGIN(mounthead, 1)

#define MOUNTHEAD_ENABLE  1
#define CCNET   "10.4.5.0"            /* network on which mounts will occur */
#define DIRS2DEL "/tmp/dirs2del_"     /* in unshared directory on each node */
#define MAXCCMNTS 8                   /* max extra mounts allowed in CCMOUNTS */
#define MNTRO   "/bin/mount -t nfs -o ro,vers=3,async,fsc,noatime,tcp,rsize=1048576,wsize=1048576"
#define MNTRW   "/bin/mount -t nfs -o rw,vers=3,async,fsc,noatime,tcp,rsize=1048576,wsize=1048576"

/* dirs not to mount ever, last is NULL */
char *nodirs[] = {"/","/dev","/lib","/lib64","/proc","/tmp","/var",'\0'};

/* dirs to mount ro on 10.4.5 network, last is NULL */
char *rodirs[] = {"/opt","/usr",'\0'};

/* dirs to mount rw on head, last is NULL */
char *rwdirs[] = {"/home",'\0'};

/* called from both srun (and slurmd? example says yes, docs say no?) */
int slurm_spank_init(spank_t sp, int ac, char **av)
{
  return 0;
}

int createpath(spank_t sp, char *path);
int exportdirs(spank_t sp, char *om);
int submithost2ip(char *submithost, char *headip);

#define P5     32
#define P7    128
#define P9    512

int slurm_spank_init_post_opt(spank_t sp, int ac, char **av)
{
  int i, n, flag;
  char buf[P9], cmd[P9], head[P7], jobid[P5], optmnts[P9], shost[P7];
  char *dir;
  struct passwd *pw;
  struct rlimit rl;
  struct rlimit *rlp= NULL;
  regex_t pattern;
  uid_t uid;
  
  /* exit if not in remote context */
  if(!spank_remote(sp)) return 0;
  
  spank_getenv(sp, "SLURM_JOB_ID", jobid, P5);
  spank_get_item(sp, S_JOB_UID, &uid);
  pw = getpwuid(uid); /* user is pw->pw_name */
  if(!pw)
  {
    slurm_error("Error looking up uid in /etc/passwd");
    return -1;
  }
  
  /* get submit host, from which mounts are made */
  head[0] = '\0';
  shost[0] = '\0';
  spank_getenv(sp, "SLURM_SUBMIT_HOST", shost, P7);
  if(submithost2ip(shost, head))
  {
    slurm_error("unable to get SUBMIT_HOST IP address for: %s %m", shost);
    return -1;
  }

  /* get optional mounts */
  optmnts[0] = '\0';
  spank_getenv(sp, "CCMOUNTS", optmnts, P9);
  
  /* set memlock limit */
  rl.rlim_cur = RLIM_INFINITY;
  rl.rlim_max = RLIM_INFINITY;
  rlp = &rl;
  if (setrlimit(RLIMIT_MEMLOCK, rlp) == -1)
  {
    slurm_error("setrlimit failed for memlock: %m");
    return -1;
  }
  
  /*
   exit quietly if we are the head, after exporting to node list on-the-fly.
   head nodes *not* in the node list (virtual machines) must explicitly
   export filesystems ahead of time, and un-export if necessary.
  */
  if(!strncmp(head, "127.0.1.1", strlen("127.0.1.1"))) /* I am head */
  {
    exportdirs(sp, optmnts);
    
    return 0;
  }
  
  /* wait for head to do exports */
  sleep(1);

  /* 
   only this process and its children will see subsequent mounts;
   when processes terminate, mounts go away automatically.
  */
  if(unshare(CLONE_NEWNS) < 0)
  {
    slurm_error("unshare CLONE_NEWNS: %m");
    return -1;
  }
  
  /* ensure that mounts are private under / */
  if(system("/bin/mount --make-private /") != 0)
  {
    slurm_error("error running mount --make-private /: %m");
    return -1;
  }
  
  /* mount ro directories from head */
  for(i=0; rodirs[i] != NULL; i++)
  {
    /* create the mount dir if needed */
    if(createpath(sp, rodirs[i]))
    {
      slurm_error("failed to create path '%s': %m", rodirs[i]);
      return -1;
    }
    else /* if the mount dir is already a mount point, ensure that it will be private */
    {
      snprintf(cmd, P9, "/bin/mountpoint -q %s", rodirs[i]);
      if(system(cmd) == 0) /* is a mountpoint */
      {
        snprintf(cmd, P9, "/bin/mount --make-private %s", rodirs[i]);
        if(system(cmd) != 0)
        {
          slurm_error("error running '%s': %m", cmd);
          return -1;
        }
      }
    }
  
    snprintf(cmd, P9, "%s %s:%s %s", MNTRO, head, rodirs[i], rodirs[i]);
    if(system(cmd) != 0)
    {
      slurm_error("error running '%s': %m", cmd);
      return -1;
    }
  }
  
  /* mount rw directories from head */
  for(i=0; rwdirs[i] != NULL; i++)
  {
    /* create the mount dir if needed */
    if(createpath(sp, rwdirs[i]))
    {
      slurm_error("failed to create path '%s': %m", rwdirs[i]);
      return -1;
    }
    else /* if the mount dir is already a mount point, ensure that it will be private */
    {
      snprintf(cmd, P9, "/bin/mountpoint -q %s", rwdirs[i]);
      if(system(cmd) == 0) /* is a mountpoint */
      {
        snprintf(cmd, P9, "/bin/mount --make-private %s", rwdirs[i]);
        if(system(cmd) != 0)
        {
          slurm_error("error running '%s': %m", cmd);
          return -1;
        }
      }
    }
  
    snprintf(cmd, P9, "%s %s:%s %s", MNTRW, head, rwdirs[i], rwdirs[i]);
    if(system(cmd) != 0)
    {
      slurm_error("error running '%s': %m", cmd);
      return -1;
    }
  }

  /* 
   mount rw filesystems on head specified by user environment variable 
   CCMOUNTS, where each directory is separated by a space, comma, or tab
   i.e. CCMOUNTS="/foo /bar" and also exported in /etc/exports.
  */
  n = 0;
  dir = NULL;
  if(optmnts[0] != '\0')
  {   
    dir = strtok(optmnts,  " ,\t");
    while(dir != NULL)
    {
      if(++n > MAXCCMNTS)
      {
        slurm_error("max number of entries (%d) in CCMOUNTS exceeded, exiting extra mount attempts...", MAXCCMNTS);
        break;
      }
      
      if(dir[0] != '/')
      {
        slurm_error("'%s' does not start with a '/', subsequent mounta aborted...", dir);
        break;
      }
      
      /* don't mount anything in NODIRS */
      flag = 0;
      for(i=0; nodirs[i] != NULL; i++)
      {
        if(!strcmp(dir, nodirs[i]))
        {
          flag = 1;
          break;
        }
      }
      
      if(flag==1)
      {
        dir = strtok(NULL,  " \t");
        continue;
      }
      
      
      /* don't remount anything in RODIRS */
      flag = 0;
      for(i=0; rodirs[i] != NULL; i++)
      {
        if(!strcmp(dir, rodirs[i]))
        {
          flag = 1;
          break;
        }
      }
      
      if(flag==1)
      {
        dir = strtok(NULL,  " \t");
        continue;
      }
        
        
      /* don't remount anything in RWDIRS */
      flag = 0;
      for(i=0; rwdirs[i] != NULL; i++)
      {
        if(!strcmp(dir, rwdirs[i]))
        {
          flag = 1;
          break;
        }
      }
      
      if(flag==1)
      {
        dir = strtok(NULL,  " \t");
        continue;
      }
      
      
      /* create the mount dir if needed */
      if(createpath(sp, dir))
      {
        slurm_error("failed to create path '%s': %m", dir);
        return -1;
      }
      
      snprintf(cmd, P9, "%s %s:%s %s", MNTRW, head, dir, dir);
      if(system(cmd) != 0)
      {
        slurm_error("error running '%s': %m", cmd);
        return -1;
      }
      
      dir = strtok(NULL,  " ,\t");
    } /* end while(dir != NULL) */
  }

  
  /* ensure '/usr/local/lib' is in library path on remote nodes */
  spank_getenv(sp, "LD_LIBRARY_PATH", buf, P9);
  regcomp(&pattern, "/usr/local/lib", REG_NOSUB);
  if(regexec(&pattern, buf, 0, NULL, 0))
  {
    if(buf[0] == '\0')
      strcat(buf,  "/usr/local/lib");
    else
      strcat(buf, ":/usr/local/lib");
    
    spank_setenv(sp, "LD_LIBRARY_PATH", buf, 1);
  }
  
  return 0;
}


/* called from both srun and slurmd */
int slurm_spank_exit(spank_t sp, int ac, char **av)
{ 
  return 0;
}


int slurm_spank_job_epilog(spank_t sp, int ac, char **av)
{
  char buf[P7], dir[P9];
  struct stat sb;
  uid_t jid;
  FILE *fp;
  
  spank_get_item(sp, S_JOB_ID, &jid);
  
  /* remove any directories that were created for mounts on remote nodes */
  snprintf(buf, P7, "%s%u", DIRS2DEL, jid);

  fp=fopen(buf, "r");
  if(fp != NULL)
  {
    while(fgets(dir, P9, fp) != NULL)
    {
      if(dir[strlen(dir)-1] == '\n') 
         dir[strlen(dir)-1]  = '\0';
         
      if(strlen(dir) > 0)
      {
        umount(dir);
        rmdir(dir);
      }
    }
    
    unlink(buf);
    fclose(fp);
  }
  
  /* unexport directories */
  snprintf(buf, P7, "%s%u%s", "/etc/exports.d/cc_", jid, ".exports");

  if(!stat(buf, &sb)) /* file exists, I must be head */
  {
    unlink(buf);
    if(system("/usr/sbin/exportfs -ra") != 0)
      slurm_error("error running '/usr/sbin/exportfs -ra': %m");
  }
  
  return 0;
}


/* 
 create a path, saving the names of dirs created 
 in reverse order so they can be removed later 
*/
int createpath(spank_t sp, char *path)
{
  int i, j;
  char dir[P9], id[P7], jobid[P5], sav[P7][P9];
  struct stat sb;
  FILE *fp;
  
  if((path[0]!='/') || (strlen(path)>P9))
  {
    slurm_error("error, path '%s' is either too long, or does not start with '/'", path);
    return -1;
  }
  
  spank_getenv(sp, "SLURM_JOB_ID", jobid, P5);
  
  for(i=0; i<P7; i++) sav[i][0]='\0';

  i = 1; j = 0;
  strncpy(dir, path, P9);
  while(i < strlen(path))
  {
    while((dir[i] != '/') && (i<strlen(path))) i++;
    dir[i] = '\0';

    if(stat(dir, &sb)) /* need to create */
    {
      if(!mkdir(dir, S_IRUSR|S_IWUSR|S_IXUSR|S_IRGRP|S_IXGRP|S_IROTH|S_IXOTH))
        strncpy(sav[j++], dir, P9);
      else
      {
        slurm_error("error, failed to create '%s': %m", dir);
        
        if(j)
        {
          /* save the dir name so it can be removed later */
          snprintf(id, P7, "%s%s", DIRS2DEL, jobid);
          fp=fopen(id, "a");
          if(fp == NULL)
          {
            slurm_error("error, failed to open '%s': %m", id);
            return -1;
          }
  
          for(i=j-1; i>=0; i--)
            fprintf(fp, "%s\n", sav[i]);
    
          fclose(fp);
        }
        
        return -1;
      }
    }
    
    dir[i] = '/';
    i++; 
    continue;
  }
  
  if(j)
  {
    snprintf(id, P7, "%s%s", DIRS2DEL, jobid);
    fp=fopen(id, "a");
    if(fp == NULL)
    {
      slurm_error("error, failed to open '%s': %m", id);
      return -1;
    }
  
    for(i=j-1; i>=0; i--)
    {
      fprintf(fp, "%s\n", sav[i]);
      printf("%s\n", sav[i]);
    }
    
    fclose(fp);
  }
  
  return 0;
}


int submithost2ip(char *submithost, char *headip)
{
  int i=0, len;
  char *net;
  struct addrinfo *sinfo, *si;
  struct sockaddr_in *sa;
 
  if(getaddrinfo(submithost, NULL, NULL, &sinfo) != 0) return 1;
 
  /* if we are not the head, use first match w/ CCNET */
  net = CCNET;
  for(len=0; len<strlen(CCNET); len++)
  {
    if(net[len] == '.') i++;
    if(i == 3) break; /* len is length of CCNET up to 3rd period */
  }
  
  for(si=sinfo; si!=NULL; si=si->ai_next) 
  {
    sa = (struct sockaddr_in *) si->ai_addr;
   
    /* I am head */
    if(!strncmp(inet_ntoa(sa->sin_addr), "127.0.1.1", strlen("127.0.1.1")))
    {
      strcpy(headip, "127.0.1.1");
      freeaddrinfo(sinfo);
      return 0;
    }
    
    /* capture head IP address if I am *not* head */
    if(!strncmp(inet_ntoa(sa->sin_addr), CCNET, len))
    {
      strcpy(headip, inet_ntoa(sa->sin_addr));
      freeaddrinfo(sinfo);
      return 0;
    }
  }
   
  return 1;
}


int exportdirs(spank_t sp, char *om)
{
  int i, n, flag;
  char cmd[P9], *dir, exfile[P9], id[P7], jobid[P5], 
       myname[P5], node[P5], nodes[P9], optmnts[P9];
  struct stat sb;
  FILE *fp, *po;
  
  if(stat("/etc/exports.d", &sb)) /* need to create */
  {
    if(mkdir("/etc/exports.d", S_IRWXU|S_IRGRP|S_IXGRP|S_IROTH|S_IXOTH)) /* 755 */
    {
      slurm_error("error, failed to create '/etc/exports.d': %m");
      return -1;
    }
  }
  
  spank_getenv(sp, "SLURM_JOB_ID", jobid, P5);
  strncpy(exfile, "/etc/exports.d/cc_", P9);
  snprintf(id, P7, "%s", jobid);
  strcat(exfile, id);
  strcat(exfile, ".exports");

  strncpy(optmnts, om, P9);
  
  /* get my node name */
  myname[0] = '\0';
  spank_getenv(sp, "SLURM_SUBMIT_HOST", myname, P5);
  if(myname[0] == '\0')
    slurm_error("unable to get SLURM_SUBMIT_HOST, continuing: %m"); /* not fatal */

  /* get node list */
  nodes[0] = '\0';
  spank_getenv(sp, "SLURM_NODELIST", nodes, P9);
  if(nodes[0] == '\0')
  {
    slurm_error("unable to get SLURM_NODELIST: %m");
    return -1;
  }
  
  /* command to expand the node list */
  snprintf(cmd, P9, "/usr/bin/scontrol show hostname  %s", nodes);
  
  fp=fopen(exfile, "w");
  if(fp != NULL)
  { 
    /* export ro directories from head */
    for(i=0; rodirs[i] != NULL; i++)
    {
      po = popen(cmd, "r");
      if (po == NULL)
      {
        slurm_error("expand nodelist error: %m");
        return -1;
      }
      
      while(fgets(node, P5-1, po) != NULL)
      {
        node[strlen(node)-1] = '\0';
        if(strcmp(myname, node))
          fprintf(fp, "%s\t%s(ro,async,root_squash,no_subtree_check)\n", rodirs[i], node);
      }
      pclose(po);
    }
    
    /* export rw directories from head */
    for(i=0; rwdirs[i] != NULL; i++)
    {
      po = popen(cmd, "r");
      if (po == NULL)
      {
        slurm_error("expand nodelist error: %m");
        return -1;
      }
      
      while(fgets(node, P5-1, po) != NULL)
      {
        node[strlen(node)-1] = '\0';
        if(strcmp(myname, node))
          fprintf(fp, "%s\t%s(rw,async,root_squash,no_subtree_check)\n", rwdirs[i], node);
      }
      pclose(po);
    }
    
    
    /* the optional directories */
    n = 0;
    dir = NULL;
    if(optmnts[0] != '\0')
    { 
      dir = strtok(optmnts,  " ,\t");
      while(dir != NULL)
      {
        if(++n > MAXCCMNTS)
        {
          slurm_error("max number of entries (%d) in CCMOUNTS exceeded, exiting extra export attempts...", MAXCCMNTS);
          break;
        }
        
        if(dir[0] != '/')
        {
          slurm_error("'%s' does not start with a '/', exiting extra export attempts...", dir);
          break;
        }
        
        /* don't export anything in NODIRS */
        flag = 0;
        for(i=0; nodirs[i] != NULL; i++)
        {
          if(!strcmp(dir, nodirs[i]))
          {
            flag = 1;
            break;
          }
        }
      
        if(flag==1)
        {
          dir = strtok(NULL,  " \t");
          continue;
        }
        
        
        /* don't re-export anything in RODIRS */
        flag = 0;
        for(i=0; rodirs[i] != NULL; i++)
        {
          if(!strcmp(dir, rodirs[i]))
          {
            flag = 1;
            break;
          }
        }
      
        if(flag==1)
        {
          dir = strtok(NULL,  " \t");
          continue;
        }
        
        /* don't re-export anything in RWDIRS */
        flag = 0;
        for(i=0; rwdirs[i] != NULL; i++)
        {
          if(!strcmp(dir, rwdirs[i]))
          {
            flag = 1;
            break;
          }
        }
      
        if(flag==1)
        {
          dir = strtok(NULL,  " \t");
          continue;
        }
        
        /* write the export */
        po = popen(cmd, "r");
        if (po == NULL)
        {
          slurm_error("expand nodelist error: %m");
          return -1;
        }
        
        while(fgets(node, P5-1, po) != NULL)
        {
          node[strlen(node)-1] = '\0';
          if(strcmp(myname, node))
            fprintf(fp, "%s\t%s(rw,async,root_squash,no_subtree_check)\n", dir, node);
        }
        pclose(po);
        
        dir = strtok(NULL,  " ,\t");
      } /* end while(dir != NULL) */
    }
    
    fclose(fp);
  }
  else
  {
    slurm_error("failed to open %s: %m", exfile);
    return -1;
  }
  
  if(system("/usr/sbin/exportfs -ra") != 0)
  {
    slurm_error("error running '/usr/sbin/exportfs -ra': %m");
    return -1;
  }
  
  return 0;
}
